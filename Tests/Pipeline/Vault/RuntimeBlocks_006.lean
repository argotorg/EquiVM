import Reasoning.Reach
import Reasoning.Immutables
import Tests.Pipeline.Vault.Bytecode
import Tests.Pipeline.Vault.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Tests.Pipeline.Vault.immutableLayout.sites = [(219, 32, "feeBps"), (1755, 32, "feeBps"), (325, 32, "owner"), (450, 32, "owner"), (1355, 32, "owner")] := by native_decide

theorem immutableLayout_inBounds :
    Tests.Pipeline.Vault.immutableLayout.inBounds Tests.Pipeline.Vault.vaultBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Tests.Pipeline.Vault.vaultBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords).size = Tests.Pipeline.Vault.vaultBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

theorem immutableDecode_1754 (immWords : String → UInt256) :
    decode (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) (⟨1754⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "feeBps", 32)) := by
  exact Layout.decodeSite (pc := (⟨1754⟩ : UInt256)) (words := immWords)
    1755 "feeBps" [(219, immWords "feeBps")] [(325, immWords "owner"), (450, immWords "owner"), (1355, immWords "owner")]
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size]; try native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize]; try native_decide
      · simp [WriteGapsOk]; try native_decide)
    (by simp [WindowDisjointFromWrites]; try native_decide)

/-- Automatically generated RD summary for bytecode block at pc 1495. -/
theorem vault_block_1495_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1529) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1495) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1529) R mem aw rdata σ (k + 8) (C + ((25) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1495⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 255) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1496⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1498⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.tload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1499⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1500⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1501⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1529) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1502⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1529), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1505⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1529)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1495_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1529) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1495) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1529) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1495_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1495. -/
theorem vault_block_1495_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1495) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1506) R mem aw rdata σ (k + 8) (C + ((25) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1495⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 255) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1496⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1498⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.tload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1499⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1500⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1501⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1529) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1502⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1529), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1505⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1506)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1495_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1495) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1506) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1495_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1506`. -/
def vault_block_1506_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 535) :: R)

/-- Final memory for bytecode block summary `vault_block_1506`. -/
def vault_block_1506_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1506. -/
theorem vault_block_1506 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2135) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1506) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2135) (vault_block_1506_stack (mem := mem) (R := R)) (vault_block_1506_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1506⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1508⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1509⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1513⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1515⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1516⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1517⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1518⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1520⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1521⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1524⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2135) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1525⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2135), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1528⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2135)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1506_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2135) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1506) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2135) (vault_block_1506_stack (mem := mem) (R := R)) (vault_block_1506_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1506 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1529. -/
theorem vault_block_1529_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1599) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1529) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1599) (x0 :: R) mem aw rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) (k + 18) (C + ((50) + (Ctload) + (Ctstore))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1529⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1530⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1532⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1533⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.tload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1534⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1535⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1537⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1538⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1539⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.or (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1540⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1541⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.tstore hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1542⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1543⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1544⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1545⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.gt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1546⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1599) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1547⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1599), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1550⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1599)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1529_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1599) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1529) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1599) (x0 :: R) mem aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1529_taken hstack hperm hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1529. -/
theorem vault_block_1529_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1529) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1551) (x0 :: R) mem aw rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) (k + 18) (C + ((50) + (Ctload) + (Ctstore))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1529⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1530⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1532⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1533⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.tload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1534⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1535⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1537⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1538⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1539⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.or (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1540⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1541⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.tstore hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1542⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1543⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1544⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1545⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.gt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1546⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1599) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1547⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1599), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1550⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1551)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1529_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1529) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1551) (x0 :: R) mem aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1529_fallthrough hstack hperm hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1551`. -/
def vault_block_1551_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 96) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) :: R)

/-- Final memory for bytecode block summary `vault_block_1551`. -/
def vault_block_1551_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 2053468783) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1551. -/
theorem vault_block_1551 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1551) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1551_stack (mem := mem) (R := R)) (vault_block_1551_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 31) (C + ((98) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1551⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1553⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1554⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1558⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1560⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1561⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1562⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1563⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1565⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1566⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1569⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1570⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1572⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1573⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1574⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1575⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1577⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1578⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1579⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1580⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push4 (UInt256.ofNat 2053468783) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1581⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2053468783), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 224) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1586⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1588⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1589⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1591⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1592⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMstore r26 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1593⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 96) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1594⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1596⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1597⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1598⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r31 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1551_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1551) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1551_stack (mem := mem) (R := R)) (vault_block_1551_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1551 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1599`. -/
def vault_block_1599_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} {gasWord0 : UInt256} : List UInt256 :=
  (gasWord0 :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 599290589) :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: R)

/-- Final memory for bytecode block summary `vault_block_1599`. -/
def vault_block_1599_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1599. -/
theorem vault_block_1599 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1599) (x0 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1667) (vault_block_1599_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R) (gasWord0 := gasWord0)) (vault_block_1599_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1599⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1600⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1601⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1602⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1604⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 599290589) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1605⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 599290589), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 224) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1610⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1612⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1613⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1614⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1615⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1616⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1618⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1619⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1620⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.address (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1621⟩ : UInt256), UInt8.ofNat 48, .ADDRESS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 36) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1622⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1624⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1625⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1626⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1627⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1629⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1630⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1631⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1632⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMstore r25 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1633⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1634⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1636⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1638⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1640⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1641⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1642⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1643⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1644⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1645⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.push4 (UInt256.ofNat 599290589) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1646⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 599290589), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1651⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 100) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1652⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1654⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1655⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1657⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := RD.genMload r41 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1659⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1660⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1661⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1662⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1663⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1664⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.dup8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1665⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := RD.genGas r48 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1666⟩ : UInt256), UInt8.ofNat 90, .GAS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1667)) r49 (by native_decide)
  exact ⟨_, _, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1599_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1599) (x0 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1667) (vault_block_1599_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R) (gasWord0 := gasWord0)) (vault_block_1599_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨gasWord0, k0, C0, h0⟩ := vault_block_1599 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨gasWord0, _, k', C', h'⟩

/- Unsupported instruction boundary at pc 1667: call (0xf1). No RD transition is asserted. Summaries resume at pc 1668 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vault_block_1668_taken`. -/
def vault_block_1668_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1668. -/
theorem vault_block_1668_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1682) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1682) (vault_block_1668_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1668⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1669⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1670⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1682) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1671⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1682), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1674⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1682)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1668_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1682) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1682) (vault_block_1668_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1668_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1668_fallthrough`. -/
def vault_block_1668_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1668. -/
theorem vault_block_1668_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1675) (vault_block_1668_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1668⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1669⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1670⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1682) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1671⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1682), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1674⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1675)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1668_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1668) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1675) (vault_block_1668_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1668_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1675. -/
theorem vault_block_1675 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1675) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1675⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1676⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1677⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1678⟩ : UInt256), UInt8.ofNat 62, .RETURNDATACOPY, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1679⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1680⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1681⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_1682`. -/
def vault_block_1682_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat rdata.size)) :: (UInt256.ofNat 1718) :: R)

/-- Final memory for bytecode block summary `vault_block_1682`. -/
def vault_block_1682_memory {mem : ByteArray} {rdata : ByteArray} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.ofNat rdata.size) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1682. -/
theorem vault_block_1682 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2238) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1682) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2238) (vault_block_1682_stack (mem := mem) (rdata := rdata) (R := R)) (vault_block_1682_memory (mem := mem) (rdata := rdata)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((81) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1682⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1683⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1684⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1685⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1686⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1687⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1689⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1690⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1691⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1693⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 31) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1694⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1696⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1697⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1698⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1699⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1700⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1701⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1702⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMstore r18 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1704⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1705⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1706⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1707⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1708⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 1718) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1709⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1718), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1712⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1713⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 2238) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1714⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2238), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1717⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2238)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1682_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2238) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1682) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2238) (vault_block_1682_stack (mem := mem) (rdata := rdata) (R := R)) (vault_block_1682_memory (mem := mem) (rdata := rdata)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1682 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1718_taken`. -/
def vault_block_1718_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1718. -/
theorem vault_block_1718_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1746) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1718) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1746) (vault_block_1718_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1718⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1746) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1719⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1746), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1722⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1746)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1718_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1746) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1718) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1746) (vault_block_1718_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1718_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1718_fallthrough`. -/
def vault_block_1718_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1718. -/
theorem vault_block_1718_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1718) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1723) (vault_block_1718_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1718⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1746) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1719⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1746), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1722⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1723)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1718_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1718) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1723) (vault_block_1718_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1718_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1723`. -/
def vault_block_1723_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 535) :: R)

/-- Final memory for bytecode block summary `vault_block_1723`. -/
def vault_block_1723_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1723. -/
theorem vault_block_1723 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2269) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1723) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2269) (vault_block_1723_stack (mem := mem) (R := R)) (vault_block_1723_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1723⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1725⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1726⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1730⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1732⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1733⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1734⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1735⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1737⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1738⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1741⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2269) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1742⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2269), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1745⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2269)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1723_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2269) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1723) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2269) (vault_block_1723_stack (mem := mem) (R := R)) (vault_block_1723_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1723 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1746`. -/
def vault_block_1746_stack {immWords : String → UInt256} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (immWords "feeBps") :: (UInt256.ofNat 1792) :: (UInt256.ofNat 10000) :: (⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1746. -/
theorem vault_block_1746 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2330) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1746) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2330) (vault_block_1746_stack (immWords := immWords) (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1746⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1747⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 10000) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1748⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10000), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1792) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1751⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1792), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (immWords "feeBps") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨1754⟩ : UInt256)
    exact immutableDecode_1754 immWords) (by evm_ov)
  have r6 := r5.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1787⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 2330) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1788⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2330), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1791⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2330)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1746_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2330) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1746) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2330) (vault_block_1746_stack (immWords := immWords) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1746 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1792`. -/
def vault_block_1792_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.ofNat 1802) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1792. -/
theorem vault_block_1792 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2353) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1792) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2353) (vault_block_1792_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1792⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1802) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1793⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1802), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1796⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1797⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2353) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1798⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2353), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1801⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2353)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1792_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2353) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1792) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2353) (vault_block_1792_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1792 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1802`. -/
def vault_block_1802_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: (UInt256.ofNat 1812) :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1802. -/
theorem vault_block_1802 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2213) (vault_block_1802_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1802⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1812) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1803⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1812), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1806⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1807⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2213) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1808⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2213), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1811⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2213)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1802_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2213) (vault_block_1802_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1802 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1812_taken`. -/
def vault_block_1812_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Final memory for bytecode block summary `vault_block_1812_taken`. -/
def vault_block_1812_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1812. -/
theorem vault_block_1812_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1901) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1812) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1901) (vault_block_1812_taken_stack (x0 := x0) (R := R)) (vault_block_1812_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1812⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1813⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1814⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1815⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1816⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1817⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1818⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1820⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1822⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1823⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1825⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1826⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1827⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1828⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1829⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1830⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1831⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1901) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1832⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1901), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1835⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1901)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1812_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1901) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1812) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1901) (vault_block_1812_taken_stack (x0 := x0) (R := R)) (vault_block_1812_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1812_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1812_fallthrough`. -/
def vault_block_1812_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Final memory for bytecode block summary `vault_block_1812_fallthrough`. -/
def vault_block_1812_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1812. -/
theorem vault_block_1812_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1812) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1836) (vault_block_1812_fallthrough_stack (x0 := x0) (R := R)) (vault_block_1812_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1812⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1813⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1814⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1815⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1816⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1817⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1818⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1820⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1822⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1823⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1825⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1826⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1827⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1828⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1829⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1830⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1831⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1901) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1832⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1901), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1835⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1836)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1812_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (⟨0⟩ : UInt256) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1812) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1836) (vault_block_1812_fallthrough_stack (x0 := x0) (R := R)) (vault_block_1812_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1812_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_1836`. -/
def vault_block_1836_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1836. -/
theorem vault_block_1836 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1836) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1901) R (vault_block_1836_memory (mem := mem)) (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (UInt256.ofNat 1))) ((UInt256.ofNat 29102676481673041902632991033461445430619272659676223336789171408008386403022) + (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (UInt256.lor (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 29102676481673041902632991033461445430619272659676223336789171408008386403022) + (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1836⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1838⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1839⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1840⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1842⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1843⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1844⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sstore r7 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1845⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1846⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1847⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1848⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1849⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMstore r12 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1850⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 29102676481673041902632991033461445430619272659676223336789171408008386403022) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1851⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 29102676481673041902632991033461445430619272659676223336789171408008386403022), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1884⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1885⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sload r16 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1886⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1887⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1889⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1891⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1893⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1894⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1895⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1896⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1897⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.or (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1898⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1899⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sstore r27 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1900⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1901)) r28 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1836_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1836) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1901) R (vault_block_1836_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (UInt256.ofNat 1))) ((UInt256.ofNat 29102676481673041902632991033461445430619272659676223336789171408008386403022) + (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (UInt256.lor (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 29102676481673041902632991033461445430619272659676223336789171408008386403022) + (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1836 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end vaultBlocks
