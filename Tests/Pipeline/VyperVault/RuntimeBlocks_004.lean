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

/-- Automatically generated RD summary for bytecode block at pc 1153. -/
theorem vyperVault_block_1153_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1153) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1153⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1553423035) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1154⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1553423035), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1159⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1160⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1161⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1164⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1153_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1153) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1153_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1153. -/
theorem vyperVault_block_1153_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1153) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1165) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1153⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1553423035) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1154⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1553423035), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1159⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1160⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1161⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1164⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1165)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1153_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1153) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1165) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1153_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1165. -/
theorem vyperVault_block_1165_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1165) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1165⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1166⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1169⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1165_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1165) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1165_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1165. -/
theorem vyperVault_block_1165_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1165) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1170) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1165⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1166⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1169⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1170)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1165_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1165) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1170) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1165_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1170. -/
theorem vyperVault_block_1170 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1170) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1170⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1172⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1173⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1175⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1176⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1178⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  exact RD.genRet r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1180⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1181. -/
theorem vyperVault_block_1181_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1211) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1181) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1181⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1182⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1187⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1188⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1211) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1189⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1211), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1192⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1211)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1181_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1211) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1181) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1181_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1181. -/
theorem vyperVault_block_1181_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1181) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1193) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1181⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1182⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1187⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1188⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1211) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1189⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1211), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1192⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1193)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1181_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1181) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1193) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1181_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1193. -/
theorem vyperVault_block_1193_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1193) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1193⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1194⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1197⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1193_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1193) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1193_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1193. -/
theorem vyperVault_block_1193_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1193) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1198) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1193⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1194⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1197⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1198)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1193_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1193) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1198) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1193_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Return the complete Vyper immutable suffix. -/
theorem vyperVault_block_1198 {immWords : String → UInt256}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1198) R mem aw rdata σ k C) :
    RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) g s0 σ (Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) := by
  have hcode : Tests.Pipeline.VyperVault.vyperVaultBytecode.size = 1429 := by native_decide
  have hsize : (Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).size = Tests.Pipeline.VyperVault.immutableLayout.size :=
    Reasoning.VyperImmutables.Layout.suffixWords_size Tests.Pipeline.VyperVault.immutableLayout immWords
  have hread : (((Tests.Pipeline.VyperVault.vyperVaultBytecode ++ Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1429).toNat mem (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) = (Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) := by
    simpa [Tests.Pipeline.VyperVault.immutableLayout, hcode] using
      Reasoning.VyperImmutables.Layout.codecopy_read_suffix (layout := Tests.Pipeline.VyperVault.immutableLayout) (template := Tests.Pipeline.VyperVault.vyperVaultBytecode)
      (mem := mem) (suffix := Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords) hsize (by decide) (UInt256.ofNat 64).toNat
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨1198⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1429) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨1200⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1429), 2))) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨1203⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨1205⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨1206⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨1208⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r7 := RD.genRet r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, Tests.Pipeline.VyperVault.immutableLayout.suffixWords immWords, (⟨1210⟩ : UInt256), .RETURN, none)) (by evm_ov)
  have hraw := r7
  rw [hread] at hraw
  exact hraw

/-- Automatically generated RD summary for bytecode block at pc 1211. -/
theorem vyperVault_block_1211_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 669136355)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1211⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 669136355) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1212⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 669136355), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1217⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1218⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1219⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1222⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1211_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 669136355)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1211_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1211. -/
theorem vyperVault_block_1211_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 669136355)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1223) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1211⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 669136355) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1212⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 669136355), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1217⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1218⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1219⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1222⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1223)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1211_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 669136355)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1223) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1211_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1223. -/
theorem vyperVault_block_1223_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1223) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1223⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1225⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1226⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1227⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1228⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1229⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1232⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1223_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1223) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1223_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1223. -/
theorem vyperVault_block_1223_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1223) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1233) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1223⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1225⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1226⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1227⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1228⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1229⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1232⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1233)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1223_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1223) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1233) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1223_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVault_block_1233_taken`. -/
def vyperVault_block_1233_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1233. -/
theorem vyperVault_block_1233_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1233) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) (vyperVault_block_1233_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1233⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1235⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1236⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1237⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1239⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1240⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1243⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1233_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1233) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) (vyperVault_block_1233_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1233_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVault_block_1233_fallthrough`. -/
def vyperVault_block_1233_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1233. -/
theorem vyperVault_block_1233_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1233) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1244) (vyperVault_block_1233_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1233⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1235⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1236⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1237⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1239⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1240⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1243⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1244)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1233_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1233) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1244) (vyperVault_block_1233_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1233_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1244. -/
theorem vyperVault_block_1244 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1244) (x0 :: R) mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 96).toNat 32).readWithPadding (UInt256.ofNat 96).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1244⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r2 := RD.genMstore r1 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1246⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1247⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1249⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r5 := RD.genMload r4 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1251⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1252⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1254⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1255⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1256⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1257⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r11 := r10.push0 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1259⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1260⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1261⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1262⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r15 := RD.genMstore r14 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1264⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1265⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1267⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  exact RD.genRet r17 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1269⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1270. -/
theorem vyperVault_block_1270_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 269060821)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1270) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1270⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 269060821) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1271⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 269060821), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1276⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1277⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1278⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1281⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1270_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 269060821)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1270) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1270_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1270. -/
theorem vyperVault_block_1270_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 269060821)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1270) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1282) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1270⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 269060821) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1271⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 269060821), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1276⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1277⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1278⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1399), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1281⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1282)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1270_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 269060821)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1270) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1282) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1270_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1282. -/
theorem vyperVault_block_1282_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1282) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1282⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1284⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1285⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1286⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1287⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1288⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1291⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1282_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1282) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1282_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1282. -/
theorem vyperVault_block_1282_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1282) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1292) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1282⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1284⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1285⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1286⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1287⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1288⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1403), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperVault.vyperVaultBytecode, suffix, (⟨1291⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1292)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVault_block_1282_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1282) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultBytecode ++ suffix) ee g s0 (UInt256.ofNat 1292) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVault_block_1282_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end vyperVaultBlocks
