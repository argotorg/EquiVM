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

/-- Final stack for bytecode block summary `vault_block_1901`. -/
def vault_block_1901_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: x0 :: (UInt256.ofNat 1931) :: (⟨0⟩ : UInt256) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) :: x0 :: x0 :: R)

/-- Final memory for bytecode block summary `vault_block_1901`. -/
def vault_block_1901_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1901. -/
theorem vault_block_1901 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2384) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1901) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2384) (vault_block_1901_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vault_block_1901_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1901⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1902⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1903⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1904⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1905⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1906⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1907⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1909⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1911⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1912⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1914⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1915⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1916⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1917⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1918⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1919⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1920⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1931) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1921⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1931), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1924⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1925⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1926⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 2384) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1927⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2384), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1930⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2384)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1901_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2384) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1901) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2384) (vault_block_1901_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vault_block_1901_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1901 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1931`. -/
def vault_block_1931_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x2 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: x4 :: (UInt256.ofNat 1955) :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 3) :: x4 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1931. -/
theorem vault_block_1931 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2384) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1931) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2384) (vault_block_1931_stack (ee := ee) (σ := σ) (x0 := x0) (x2 := x2) (x4 := x4) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1931⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1932⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1933⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1934⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1935⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1936⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sstore r6 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1937⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1938⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1939⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 3) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1940⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1942⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1943⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1944⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1945⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1955) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1946⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1955), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1949⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1950⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 2384) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1951⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2384), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1954⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2384)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1931_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2384) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1931) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2384) (vault_block_1931_stack (ee := ee) (σ := σ) (x0 := x0) (x2 := x2) (x4 := x4) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1931 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1955`. -/
def vault_block_1955_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1955`. -/
def vault_block_1955_memory {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  (x4.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1955. -/
theorem vault_block_1955 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x6 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1955) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x6 (vault_block_1955_stack (R := R)) (vault_block_1955_memory (mem := mem) (x4 := x4)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) (UInt256.sub ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)))) rdata (tstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x2 x0) (⟨0⟩ : UInt256) (UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 255)))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1955⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1956⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1957⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1958⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1959⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1960⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1961⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMload r7 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1963⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1964⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1965⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1966⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.caller (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1967⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1968⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 102222681472383059465863322013072701928378550215632170212813623808969952268444) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨1969⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 102222681472383059465863322013072701928378550215632170212813623808969952268444), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2002⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2003⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2005⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2006⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMload r18 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2008⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2009⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2010⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2011⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2012⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genLog2 r23 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2013⟩ : UInt256), UInt8.ofNat 162, .LOG2, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r25 := r24.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2014⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2015⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 255) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2016⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.not (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2018⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2019⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.tload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2020⟩ : UInt256), UInt8.ofNat 92, .TLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2021⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2022⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.tstore hperm (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2023⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2024⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2025⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2026⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact ⟨_, _, r36⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1955_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x6 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 1955) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x6 (vault_block_1955_stack (R := R)) (vault_block_1955_memory (mem := mem) (x4 := x4)) aw' rdata (tstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x2 x0) (⟨0⟩ : UInt256) (UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 255)))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1955 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2027_taken`. -/
def vault_block_2027_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 2) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2027. -/
theorem vault_block_2027_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2042) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2027) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2042) (vault_block_2027_taken_stack (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2027⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2028⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2030⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2031⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2032⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2033⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.lt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2034⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 2042) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2035⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2042), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2038⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2042)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2027_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2042) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2027) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2042) (vault_block_2027_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_2027_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2027_fallthrough`. -/
def vault_block_2027_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 2) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2027. -/
theorem vault_block_2027_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2027) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2039) (vault_block_2027_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2027⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2028⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2030⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2031⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2032⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2033⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.lt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2034⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 2042) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2035⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2042), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2038⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2039)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2027_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2027) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2039) (vault_block_2027_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_2027_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2039. -/
theorem vault_block_2039 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2039) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2039⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2040⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2041⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_2042`. -/
def vault_block_2042_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 32) (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)) + x0) (⟨0⟩ : UInt256)))) :: x3 :: R)

/-- Final memory for bytecode block summary `vault_block_2042`. -/
def vault_block_2042_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2042. -/
theorem vault_block_2042 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x3 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2042) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x3 (vault_block_2042_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) (vault_block_2042_memory (mem := mem) (x1 := x1)) (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2042⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2043⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2044⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2045⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2046⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2047⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2049⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2050⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2051⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2052⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2053⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2054⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2056⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2058⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2060⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2061⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2062⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2063⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2064⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2065⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2066⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact ⟨_, _, r21⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2042_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x3 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2042) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x3 (vault_block_2042_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) (vault_block_2042_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_2042 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2067_taken`. -/
def vault_block_2067_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2067. -/
theorem vault_block_2067_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2083) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2067) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2083) (vault_block_2067_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2067⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2068⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2069⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2071⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2072⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2073⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2074⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2075⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2083) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2076⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2083), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2079⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2083)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2067_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2083) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2067) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2083) (vault_block_2067_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2067_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2067_fallthrough`. -/
def vault_block_2067_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2067. -/
theorem vault_block_2067_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2067) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2080) (vault_block_2067_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2067⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2068⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2069⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2071⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2072⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2073⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2074⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2075⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2083) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2076⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2083), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2079⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2080)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2067_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2067) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2080) (vault_block_2067_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2067_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2080. -/
theorem vault_block_2080 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2080) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2080⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2081⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2082⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_2083_taken`. -/
def vault_block_2083_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2083. -/
theorem vault_block_2083_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2105) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2083) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2105) (vault_block_2083_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2083⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2084⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2085⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2086⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2088⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2090⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2092⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2093⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2094⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2095⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2096⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2097⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 2105) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2098⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2105), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2101⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2105)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2083_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2105) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2083) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2105) (vault_block_2083_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2083_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2083_fallthrough`. -/
def vault_block_2083_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2083. -/
theorem vault_block_2083_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2083) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2102) (vault_block_2083_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2083⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2084⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2085⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2086⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2088⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2090⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2092⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2093⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2094⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2095⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2096⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.eq (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2097⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 2105) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2098⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2105), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2101⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2102)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2083_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2083) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2102) (vault_block_2083_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2083_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2102. -/
theorem vault_block_2102 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2102) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2102⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2103⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2104⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_2105`. -/
def vault_block_2105_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2105. -/
theorem vault_block_2105 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x4 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2105) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x4 (vault_block_2105_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2105⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2106⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2107⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2108⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2109⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2110⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2111⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2105_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x4 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2105) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x4 (vault_block_2105_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2105 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2112_taken`. -/
def vault_block_2112_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2112. -/
theorem vault_block_2112_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2128) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2112) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2128) (vault_block_2112_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2112⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2113⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2114⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2116⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2117⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2118⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2119⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2120⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2128) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2121⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2128), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2124⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2128)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2112_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2128) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2112) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2128) (vault_block_2112_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2112_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2112_fallthrough`. -/
def vault_block_2112_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2112. -/
theorem vault_block_2112_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2112) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2125) (vault_block_2112_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2112⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2113⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2114⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2116⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2117⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2118⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2119⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2120⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2128) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2121⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2128), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2124⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2125)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2112_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2112) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2125) (vault_block_2112_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2112_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2125. -/
theorem vault_block_2125 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2125) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2125⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2126⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2127⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_2128`. -/
def vault_block_2128_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2128. -/
theorem vault_block_2128 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x3 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2128) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x3 (vault_block_2128_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2128⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2129⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldataload (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2130⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2131⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2132⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2133⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2134⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2128_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x3 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2128) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x3 (vault_block_2128_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2128 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2135`. -/
def vault_block_2135_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 96) + x0) :: R)

/-- Final memory for bytecode block summary `vault_block_2135`. -/
def vault_block_2135_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 527558797954945407901) (UInt256.ofNat 186)).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) (x0 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2135. -/
theorem vault_block_2135 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x1 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2135) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x1 (vault_block_2135_stack (x0 := x0) (R := R)) (vault_block_2135_memory (mem := mem) (x0 := x0)) (M (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((66) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2135⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2136⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2138⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2139⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2140⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 9) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2141⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 9), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2143⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2144⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2145⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2146⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 527558797954945407901) (width := 9) (op := .PUSH9) (by decide) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2147⟩ : UInt256), UInt8.ofNat 104, .Push .PUSH9, some ((UInt256.ofNat 527558797954945407901), 9), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 186) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2157⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 186), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2159⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2160⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2162⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2163⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2164⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 96) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2165⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2167⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap1 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2168⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jump (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2169⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r21 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2135_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains x1 = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2135) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 x1 (vault_block_2135_stack (x0 := x0) (R := R)) (vault_block_2135_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2135 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2170_taken`. -/
def vault_block_2170_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2170. -/
theorem vault_block_2170_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2186) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2170) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2186) (vault_block_2170_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2170⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2171⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2172⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2174⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2175⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2176⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2177⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.iszero (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2178⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2186) (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2179⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2186), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Tests.Pipeline.Vault.immutableLayout, Tests.Pipeline.Vault.vaultBytecode, immWords, (⟨2182⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2186)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2170_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) 0).contains (UInt256.ofNat 2186) = true)
    (h : RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2170) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.immutableLayout.runtime Tests.Pipeline.Vault.vaultBytecode immWords) ee g s0 (UInt256.ofNat 2186) (vault_block_2170_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2170_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end vaultBlocks
