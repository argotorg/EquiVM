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

theorem immutableDecode_1354 (immWords : String → UInt256) :
    decode (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) (⟨1354⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "owner", 32)) := by
  exact Layout.decodeSite (pc := (⟨1354⟩ : UInt256)) (words := immWords)
    1355 "owner" [(219, immWords "feeBps"), (1755, immWords "feeBps"), (325, immWords "owner"), (450, immWords "owner")] []
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

/-- Final memory for bytecode block summary `vault_block_987_fallthrough`. -/
def vault_block_987_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 987. -/
theorem vault_block_987_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.gt x0 ((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 987) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1024) (x0 :: R) (vault_block_987_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨987⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨988⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨990⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨991⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.tload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨992⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨993⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨995⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨996⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨997⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.or (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨998⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨999⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.tstore hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1000⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1001⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1002⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1003⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1004⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1005⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMstore r17 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1006⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1007⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1009⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genMstore r20 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1011⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1012⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1014⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1015⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1016⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1017⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.gt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1018⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1019⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 1078) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1020⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1078), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1023⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1024)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_987_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.gt x0 ((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 987) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1024) (x0 :: R) (vault_block_987_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_987_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1024`. -/
def vault_block_1024_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `vault_block_1024`. -/
def vault_block_1024_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 8157363277298032243430218653) (UInt256.ofNat 162)).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1024. -/
theorem vault_block_1024 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1024) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1024_stack (mem := mem) (R := R)) (vault_block_1024_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((89) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1024⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1026⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1027⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1031⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1033⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1034⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1035⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1036⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1038⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1040⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1041⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1042⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 12) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1043⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 12), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1045⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1047⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1048⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1049⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 8157363277298032243430218653) (width := 12) (op := .PUSH12) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1050⟩ : UInt256), UInt8.ofNat 107, .Push .PUSH12, some ((UInt256.ofNat 8157363277298032243430218653), 12), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 162) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1063⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 162), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1065⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1066⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1068⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1069⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genMstore r23 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1070⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 100) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1071⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1073⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1074⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1077⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1024_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1024) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1024_stack (mem := mem) (R := R)) (vault_block_1024_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1024 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1078`. -/
def vault_block_1078_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: x0 :: (UInt256.ofNat 1108) :: (⟨0⟩ : UInt256) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) :: x0 :: x0 :: R)

/-- Final memory for bytecode block summary `vault_block_1078`. -/
def vault_block_1078_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1078. -/
theorem vault_block_1078 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1078) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2213) (vault_block_1078_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vault_block_1078_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1078⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1079⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1080⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1081⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1082⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1083⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1084⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1086⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1088⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1089⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1091⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1092⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1093⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1094⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1095⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1096⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1097⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1108) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1098⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1108), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1101⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1102⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1103⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 2213) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1104⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2213), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1107⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2213)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1078_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1078) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2213) (vault_block_1078_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vault_block_1078_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1078 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1108`. -/
def vault_block_1108_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x2 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: x4 :: (UInt256.ofNat 1132) :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 3) :: x4 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1108. -/
theorem vault_block_1108 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1108) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2213) (vault_block_1108_stack (ee := ee) (σ := σ) (x0 := x0) (x2 := x2) (x4 := x4) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1108⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1109⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1110⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1111⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1112⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1113⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sstore r6 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1114⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1115⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1116⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 3) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1117⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1119⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1120⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1121⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1122⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1132) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1123⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1132), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1126⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1127⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 2213) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1128⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2213), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1131⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2213)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1108_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1108) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2213) (vault_block_1108_stack (ee := ee) (σ := σ) (x0 := x0) (x2 := x2) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1108 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1132`. -/
def vault_block_1132_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x2 : UInt256} {x4 : UInt256} {R : List UInt256} {gasWord0 : UInt256} : List UInt256 :=
  (gasWord0 :: (UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 2835717307) :: (UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x4 :: R)

/-- Final memory for bytecode block summary `vault_block_1132`. -/
def vault_block_1132_memory {ee : ExecutionEnv} {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  (x4.toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1132. -/
theorem vault_block_1132 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1132) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1199) (vault_block_1132_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x2 := x2) (x4 := x4) (R := R) (gasWord0 := gasWord0)) (vault_block_1132_memory (ee := ee) (mem := mem) (x4 := x4)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1132⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1133⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1134⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1135⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1136⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1137⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1138⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1139⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1140⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMload r9 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1142⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push4 (UInt256.ofNat 2835717307) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1143⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2835717307), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 224) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1148⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1150⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1151⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1152⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1153⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1154⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1156⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1157⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1158⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 36) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1159⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1161⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1162⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1163⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1164⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMstore r25 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1165⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1166⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1168⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1170⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1172⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1173⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1174⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1175⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1176⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1177⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.push4 (UInt256.ofNat 2835717307) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1178⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2835717307), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1183⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 68) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1184⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1186⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1187⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1189⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := RD.genMload r41 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1191⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1192⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1193⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1194⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1195⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1196⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.dup8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1197⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := RD.genGas r48 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1198⟩ : UInt256), UInt8.ofNat 90, .GAS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1199)) r49 (by native_decide)
  exact ⟨_, _, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1132_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1132) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1199) (vault_block_1132_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x2 := x2) (x4 := x4) (R := R) (gasWord0 := gasWord0)) (vault_block_1132_memory (ee := ee) (mem := mem) (x4 := x4)) aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨gasWord0, k0, C0, h0⟩ := vault_block_1132 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨gasWord0, _, k', C', h'⟩

/- Unsupported instruction boundary at pc 1199: call (0xf1). No RD transition is asserted. Summaries resume at pc 1200 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vault_block_1200_taken`. -/
def vault_block_1200_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1200. -/
theorem vault_block_1200_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1214) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1200) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1214) (vault_block_1200_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1200⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1201⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1202⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1214) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1203⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1214), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1206⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1214)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1200_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1214) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1200) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1214) (vault_block_1200_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1200_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1200_fallthrough`. -/
def vault_block_1200_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1200. -/
theorem vault_block_1200_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1200) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1207) (vault_block_1200_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1200⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1201⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1202⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1214) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1203⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1214), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1206⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1207)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1200_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1200) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1207) (vault_block_1200_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1200_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1207. -/
theorem vault_block_1207 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1207) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1207⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1208⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1209⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1210⟩ : UInt256), UInt8.ofNat 62, .RETURNDATACOPY, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1211⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1212⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1213⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_1214`. -/
def vault_block_1214_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat rdata.size)) :: (UInt256.ofNat 1250) :: R)

/-- Final memory for bytecode block summary `vault_block_1214`. -/
def vault_block_1214_memory {mem : ByteArray} {rdata : ByteArray} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.ofNat rdata.size) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1214. -/
theorem vault_block_1214 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2238) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1214) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2238) (vault_block_1214_stack (mem := mem) (rdata := rdata) (R := R)) (vault_block_1214_memory (mem := mem) (rdata := rdata)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((81) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1214⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1215⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1216⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1217⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1218⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1219⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1221⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.returndatasize (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1222⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1223⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1225⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 31) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1226⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 31), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1228⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1229⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1230⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1231⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1232⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1233⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1234⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMstore r18 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1236⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1237⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1238⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1239⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1240⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 1250) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1241⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1250), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1244⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1245⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 2238) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1246⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2238), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1249⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2238)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1214_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2238) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1214) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2238) (vault_block_1214_stack (mem := mem) (rdata := rdata) (R := R)) (vault_block_1214_memory (mem := mem) (rdata := rdata)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1214 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1250_taken`. -/
def vault_block_1250_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1250. -/
theorem vault_block_1250_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1278) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1250) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1278) (vault_block_1250_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1250⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1278) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1251⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1278), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1254⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1278)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1250_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1278) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1250) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1278) (vault_block_1250_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1250_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1250_fallthrough`. -/
def vault_block_1250_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1250. -/
theorem vault_block_1250_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1250) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1255) (vault_block_1250_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1250⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1278) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1251⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1278), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1254⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1255)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1250_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1250) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1255) (vault_block_1250_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1250_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1255`. -/
def vault_block_1255_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 535) :: R)

/-- Final memory for bytecode block summary `vault_block_1255`. -/
def vault_block_1255_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1255. -/
theorem vault_block_1255 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2269) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1255) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2269) (vault_block_1255_stack (mem := mem) (R := R)) (vault_block_1255_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1255⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1257⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1258⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1262⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1264⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1265⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1266⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1267⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1269⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1270⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1273⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2269) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1274⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2269), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1277⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2269)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1255_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2269) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1255) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2269) (vault_block_1255_stack (mem := mem) (R := R)) (vault_block_1255_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1255 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1278`. -/
def vault_block_1278_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1278`. -/
def vault_block_1278_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1278. -/
theorem vault_block_1278 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x1 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1278) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x1 (vault_block_1278_stack (R := R)) (vault_block_1278_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) (UInt256.sub ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)))) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 255)))) (k + 30) (C + ((80) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) (UInt256.sub ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)))) + (375 + 8 * (UInt256.sub ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))).toNat + 2 * 375) + (Ctload) + (Ctstore))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1278⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1279⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1281⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1282⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1283⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1284⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1285⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1286⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 61653871931129225497400619673525043252581014578873288143200065866771265110884) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1287⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 61653871931129225497400619673525043252581014578873288143200065866771265110884), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1320⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1321⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1323⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1324⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMload r13 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1326⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1327⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1328⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1329⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1330⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genLog2 r18 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1331⟩ : UInt256), UInt8.ofNat 162, .LOG2, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r20 := r19.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1332⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 255) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1333⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1335⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1336⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.tload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1337⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1338⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1339⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.tstore hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1340⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1341⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1342⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1343⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r30 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1278_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x1 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1278) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x1 (vault_block_1278_stack (R := R)) (vault_block_1278_memory (mem := mem) (x0 := x0)) aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 255)))) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1278 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1344. -/
theorem vault_block_1344_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1444) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1344) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1444) R mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1344⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1345⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1346⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1348⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1350⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1352⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1353⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (immWords "owner") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨1354⟩ : UInt256)
    exact immutableDecode_1354 immWords) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1387⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1388⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 1444) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1389⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1444), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1392⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1444)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1344_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1444) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1344) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1444) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1344_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1344. -/
theorem vault_block_1344_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1344) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1393) R mem aw rdata σ (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1344⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1345⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1346⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1348⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1350⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1352⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1353⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (immWords "owner") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨1354⟩ : UInt256)
    exact immutableDecode_1354 immWords) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1387⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1388⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 1444) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1389⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1444), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1392⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1393)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1344_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.land (immWords "owner") (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1344) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1393) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1344_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1393`. -/
def vault_block_1393_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `vault_block_1393`. -/
def vault_block_1393_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1018586463903338148537) (UInt256.ofNat 185)).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1393. -/
theorem vault_block_1393 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1393) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1393_stack (mem := mem) (R := R)) (vault_block_1393_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((89) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1393⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1395⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1396⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 4594637), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1400⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 229), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1402⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1403⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1404⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1405⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 4) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1407⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1409⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1410⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1411⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 9) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1412⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 9), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1414⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1416⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1417⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1418⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 1018586463903338148537) (width := 9) (op := .PUSH9) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1419⟩ : UInt256), UInt8.ofNat 104, .Push .PUSH9, some ((UInt256.ofNat 1018586463903338148537), 9), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 185) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1429⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 185), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1431⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1432⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 68), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1434⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1435⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genMstore r23 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1436⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 100) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1437⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 100), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1439⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 535) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1440⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 535), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1443⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1393_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1393) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 535) (vault_block_1393_stack (mem := mem) (R := R)) (vault_block_1393_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1393 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1444_taken`. -/
def vault_block_1444_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 2) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1444. -/
theorem vault_block_1444_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1461) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1444) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1461) (vault_block_1444_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1444⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1445⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1447⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1448⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1449⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1461) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1450⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1461), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1453⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1461)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1444_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 1461) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1444) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1461) (vault_block_1444_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1444_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1444_fallthrough`. -/
def vault_block_1444_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 2) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1444. -/
theorem vault_block_1444_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1444) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1454) (vault_block_1444_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1444⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1445⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1447⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1448⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1449⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1461) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1450⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1461), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1453⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1454)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1444_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1444) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1454) (vault_block_1444_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1444_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1454`. -/
def vault_block_1454_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1461) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1454. -/
theorem vault_block_1454 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2310) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1454) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2310) (vault_block_1454_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1461) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1454⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1461), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2310) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1457⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2310), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1460⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2310)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1454_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2310) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1454) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2310) (vault_block_1454_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1454 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1461`. -/
def vault_block_1461_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1461`. -/
def vault_block_1461_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1461. -/
theorem vault_block_1461 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x2 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1461) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x2 (vault_block_1461_stack (R := R)) (vault_block_1461_memory (mem := mem) (x1 := x1)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (⟨0⟩ : UInt256))))) x1 ((UInt256.lnot (⟨0⟩ : UInt256)) + x0)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1461⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1462⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1463⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1464⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1465⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1466⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1468⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genKeccak256 r7 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1469⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1470⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1471⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1472⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1473⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1474⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1475⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1476⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1477⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sload r16 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1478⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1479⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1481⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1483⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1485⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1486⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1487⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1488⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1489⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r26⟩ := RD.sstore r25 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1490⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1491⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1492⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sstore r28 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1493⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1494⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact ⟨_, _, r30⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1461_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x2 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1461) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x2 (vault_block_1461_stack (R := R)) (vault_block_1461_memory (mem := mem) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.lnot (⟨0⟩ : UInt256)) + (x0 + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)))) (⟨0⟩ : UInt256))))) x1 ((UInt256.lnot (⟨0⟩ : UInt256)) + x0)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1461 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end vaultBlocks
