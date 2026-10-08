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
    Tests.Pipeline.Vault.immutableLayout.sites = [(219, 32, "feeBps"), (1591, 32, "feeBps"), (325, 32, "owner"), (450, 32, "owner"), (1239, 32, "owner")] := by native_decide

theorem immutableLayout_inBounds :
    Tests.Pipeline.Vault.immutableLayout.inBounds Tests.Pipeline.Vault.vaultBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Tests.Pipeline.Vault.vaultBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords).size = Tests.Pipeline.Vault.vaultBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

theorem immutableDecode_1238 (immWords : String → UInt256) :
    decode (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) (⟨1238⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "owner", 32)) := by
  exact Layout.decodeSite (pc := (⟨1238⟩ : UInt256)) (words := immWords)
    1239 "owner" [(219, immWords "feeBps"), (1591, immWords "feeBps"), (325, immWords "owner"), (450, immWords "owner")] []
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

/-- Final stack for bytecode block summary `vault_block_1094_fallthrough`. -/
def vault_block_1094_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1094. -/
theorem vault_block_1094_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1094) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1101) (vault_block_1094_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1094⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1095⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1096⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1108) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1097⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1108), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1100⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1101)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1094_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1094) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1101) (vault_block_1094_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1094_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1101. -/
theorem vault_block_1101 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1101) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1101⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1102⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1103⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1104⟩ : UInt256), UInt8.ofNat 62, .RETURNDATACOPY, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1105⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1106⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1107⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_1108`. -/
def vault_block_1108_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat rdata.size)) :: (UInt256.ofNat 1144) :: R)

/-- Final memory for bytecode block summary `vault_block_1108`. -/
def vault_block_1108_memory {mem : ByteArray} {rdata : ByteArray} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.ofNat rdata.size) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1108. -/
theorem vault_block_1108 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2029) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1108) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2029) (vault_block_1108_stack (mem := mem) (rdata := rdata) (R := R)) (vault_block_1108_memory (mem := mem) (rdata := rdata)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((81) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1108⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1109⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1110⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1111⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1112⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1113⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1115⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1116⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1117⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1119⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 31) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1120⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1122⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1123⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1124⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1125⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1126⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1127⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1128⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMstore r18 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1130⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1131⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1132⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1133⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1134⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 1144) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1135⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1144), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1138⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1139⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 2029) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1140⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2029), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1143⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2029)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1108_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2029) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1108) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2029) (vault_block_1108_stack (mem := mem) (rdata := rdata) (R := R)) (vault_block_1108_memory (mem := mem) (rdata := rdata)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1108 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1144_taken`. -/
def vault_block_1144_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1144. -/
theorem vault_block_1144_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1172) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1144) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1172) (vault_block_1144_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1144⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1172) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1145⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1172), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1148⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1172)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1144_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1172) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1144) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1172) (vault_block_1144_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1144_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1144_fallthrough`. -/
def vault_block_1144_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1144. -/
theorem vault_block_1144_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1144) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1149) (vault_block_1144_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1144⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1172) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1145⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1172), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1148⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1149)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1144_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1144) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1149) (vault_block_1144_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1144_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1149`. -/
def vault_block_1149_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 535) :: R)

/-- Final memory for bytecode block summary `vault_block_1149`. -/
def vault_block_1149_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1149. -/
theorem vault_block_1149 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2060) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1149) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2060) (vault_block_1149_stack (mem := mem) (R := R)) (vault_block_1149_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1149⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1151⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1152⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1156⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1158⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1159⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1160⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1161⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1163⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1164⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1167⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2060) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1168⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2060), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1171⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2060)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1149_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2060) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1149) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2060) (vault_block_1149_stack (mem := mem) (R := R)) (vault_block_1149_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1149 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1172`. -/
def vault_block_1172_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1172`. -/
def vault_block_1172_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1172. -/
theorem vault_block_1172 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x1 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1172) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x1 (vault_block_1172_stack (R := R)) (vault_block_1172_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) (UInt256.sub ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)))) rdata σ (k + 21) (C + ((61) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) (UInt256.sub ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)))) + (375 + 8 * (UInt256.sub ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))).toNat + 2 * 375))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1172⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1173⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1175⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1176⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1177⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1178⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1179⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1180⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 61653871931129225497400619673525043252581014578873288143200065866771265110884) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1181⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 61653871931129225497400619673525043252581014578873288143200065866771265110884), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1214⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1215⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1217⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1218⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMload r13 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1220⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1221⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1222⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1223⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1224⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genLog2 r18 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1225⟩ : UInt256), UInt8.ofNat 162, .LOG2, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r20 := r19.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1226⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1227⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r21 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1172_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x1 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1172) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x1 (vault_block_1172_stack (R := R)) (vault_block_1172_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1172 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1228. -/
theorem vault_block_1228_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1328) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1228) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1328) R mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1228⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1229⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1230⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1232⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1234⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1236⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1237⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (immWords "owner") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨1238⟩ : UInt256)
    exact immutableDecode_1238 immWords) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1271⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1272⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 1328) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1273⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1328), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1276⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1328)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1228_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1328) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1228) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1328) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1228_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1228. -/
theorem vault_block_1228_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1228) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1277) R mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1228⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1229⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1230⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1232⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1234⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1236⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1237⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (immWords "owner") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨1238⟩ : UInt256)
    exact immutableDecode_1238 immWords) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1271⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1272⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 1328) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1273⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1328), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1276⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1277)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1228_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1228) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1277) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1228_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1277`. -/
def vault_block_1277_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `vault_block_1277`. -/
def vault_block_1277_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1018586463903338148537) (UInt256.ofNat 185)).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1277. -/
theorem vault_block_1277 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1277) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1277_stack (mem := mem) (R := R)) (vault_block_1277_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((89) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1277⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1279⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1280⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1284⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1286⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1287⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1288⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1289⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1291⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1293⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1294⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1295⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 9) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1296⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 9), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1298⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1300⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1301⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1302⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 1018586463903338148537) (width := 9) (op := .PUSH9) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1303⟩ : UInt256), UInt8.ofNat 104, .Push .PUSH9, some ((UInt256.ofNat 1018586463903338148537), 9), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 185) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1313⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 185), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1315⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1316⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1318⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1319⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genMstore r23 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1320⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 100) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1321⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1323⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1324⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1327⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1277_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1277) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1277_stack (mem := mem) (R := R)) (vault_block_1277_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1277 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1328_taken`. -/
def vault_block_1328_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 2) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1328. -/
theorem vault_block_1328_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1345) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1328) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1345) (vault_block_1328_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1328⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1329⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1331⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1332⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1333⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1345) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1334⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1345), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1337⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1345)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1328_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1345) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1328) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1345) (vault_block_1328_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1328_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1328_fallthrough`. -/
def vault_block_1328_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 2) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1328. -/
theorem vault_block_1328_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1328) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1338) (vault_block_1328_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1328⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1329⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1331⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1332⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1333⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1345) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1334⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1345), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1337⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1338)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1328_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1328) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1338) (vault_block_1328_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1328_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1338`. -/
def vault_block_1338_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1345) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1338. -/
theorem vault_block_1338 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2101) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1338) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2101) (vault_block_1338_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1345) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1338⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1345), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2101) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1341⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2101), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1344⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2101)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1338_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2101) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1338) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2101) (vault_block_1338_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1338 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1345`. -/
def vault_block_1345_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1345`. -/
def vault_block_1345_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1345. -/
theorem vault_block_1345 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x2 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1345) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x2 (vault_block_1345_stack (R := R)) (vault_block_1345_memory (mem := mem) (x1 := x1)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (⟨0⟩ : UInt256))))) x1 ((UInt256.lnot (⟨0⟩ : UInt256)) + x0)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1345⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1346⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1347⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1348⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1349⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1350⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1352⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genKeccak256 r7 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1353⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1354⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1355⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1356⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1357⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1358⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1359⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1360⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1361⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sload r16 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1362⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1363⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1365⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1367⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1369⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1370⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1371⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1372⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1373⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r26⟩ := RD.sstore r25 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1374⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1375⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1376⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sstore r28 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1377⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1378⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact ⟨_, _, r30⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1345_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x2 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1345) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x2 (vault_block_1345_stack (R := R)) (vault_block_1345_memory (mem := mem) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (⟨0⟩ : UInt256))))) x1 ((UInt256.lnot (⟨0⟩ : UInt256)) + x0)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1345 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1379. -/
theorem vault_block_1379_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1435) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1435) (x0 :: R) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1379⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1380⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1381⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.gt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1382⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1435) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1383⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1435), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1386⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1435)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1379_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1435) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1435) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1379_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1379. -/
theorem vault_block_1379_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1387) (x0 :: R) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1379⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1380⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1381⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.gt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1382⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1435) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1383⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1435), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1386⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1387)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1379_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1387) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1379_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1387`. -/
def vault_block_1387_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 96) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) :: R)

/-- Final memory for bytecode block summary `vault_block_1387`. -/
def vault_block_1387_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 2053468783) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1387. -/
theorem vault_block_1387 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1387) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1387_stack (mem := mem) (R := R)) (vault_block_1387_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 31) (C + ((98) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1387⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1389⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1390⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1394⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1396⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1397⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1398⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1399⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1401⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1402⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1405⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1406⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1408⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1409⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1410⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1411⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1413⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1414⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1415⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1416⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push4 (UInt256.ofNat 2053468783) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1417⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2053468783), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 224) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1422⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1424⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1425⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1427⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1428⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMstore r26 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1429⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 96) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1430⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1432⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1433⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1434⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r31 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1387_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1387) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1387_stack (mem := mem) (R := R)) (vault_block_1387_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1387 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1435`. -/
def vault_block_1435_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} {gasWord0 : UInt256} : List UInt256 :=
  (gasWord0 :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 599290589) :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: R)

/-- Final memory for bytecode block summary `vault_block_1435`. -/
def vault_block_1435_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 599290589) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1435. -/
theorem vault_block_1435 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1435) (x0 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1503) (vault_block_1435_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R) (gasWord0 := gasWord0)) (vault_block_1435_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1435⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1436⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1437⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1438⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1440⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push4 (UInt256.ofNat 599290589) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1441⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 599290589), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 224) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1446⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1448⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1449⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1450⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1451⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1452⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1454⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1455⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1456⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.address (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1457⟩ : UInt256), UInt8.ofNat 48, .ADDRESS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 36) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1458⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1460⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1461⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1462⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1463⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1465⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1466⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1467⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1468⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMstore r25 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1469⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1470⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1472⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1474⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1476⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1477⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1478⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1479⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1480⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1481⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.push4 (UInt256.ofNat 599290589) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1482⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 599290589), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1487⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 100) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1488⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1490⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1491⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1493⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := RD.genMload r41 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1495⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1496⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1497⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1498⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1499⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1500⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.dup8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1501⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := RD.genGas r48 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1502⟩ : UInt256), UInt8.ofNat 90, .GAS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1503)) r49 (by native_decide)
  exact ⟨_, _, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1435_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1435) (x0 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1503) (vault_block_1435_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R) (gasWord0 := gasWord0)) (vault_block_1435_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨gasWord0, k0, C0, h0⟩ := vault_block_1435 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨gasWord0, _, k', C', h'⟩

/- Unsupported instruction boundary at pc 1503: call (0xf1). No RD transition is asserted. Summaries resume at pc 1504 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vault_block_1504_taken`. -/
def vault_block_1504_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1504. -/
theorem vault_block_1504_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1518) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1504) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1518) (vault_block_1504_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1504⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1505⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1506⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1518) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1507⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1518), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1510⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1518)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1504_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1518) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1504) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1518) (vault_block_1504_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1504_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1504_fallthrough`. -/
def vault_block_1504_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1504. -/
theorem vault_block_1504_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1504) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1511) (vault_block_1504_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1504⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1505⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1506⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1518) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1507⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1518), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1510⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1511)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1504_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1504) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1511) (vault_block_1504_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1504_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end vaultBlocks
