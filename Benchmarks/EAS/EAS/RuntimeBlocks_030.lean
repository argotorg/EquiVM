import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.EAS.EAS.Bytecode
import Benchmarks.EAS.EAS.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace easBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.EAS.EAS.immutableLayout.sites = [(14029, 32, "_CACHED_DOMAIN_SEPARATOR"), (14218, 32, "_CACHED_CHAIN_ID"), (13982, 32, "_CACHED_THIS"), (14108, 32, "_HASHED_NAME"), (14146, 32, "_HASHED_VERSION"), (14073, 32, "_TYPE_HASH"), (678, 32, "_schemaRegistry"), (7761, 32, "_schemaRegistry"), (9982, 32, "_schemaRegistry"), (12162, 32, "_schemaRegistry"), (12821, 32, "_schemaRegistry")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.EAS.EAS.immutableLayout.inBounds Benchmarks.EAS.EAS.easBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.EAS.EAS.easBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size = Benchmarks.EAS.EAS.easBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `eas_block_7853`. -/
def eas_block_7853_stack {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x6 :: x7 :: x8 :: (UInt256.ofNat 1) :: (UInt256.ofNat 7871) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7853. -/
theorem eas_block_7853 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14435) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7853) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14435) (eas_block_7853_stack (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 13) (C + ((39))) := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7853⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7854⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7855⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7856⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7857⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7858⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 7871) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7859⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7871), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7862⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7863⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7864⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7866⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 14435) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7867⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14435), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7870⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14435)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7853_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14435) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7853) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14435) (eas_block_7853_stack (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7853 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7871`. -/
def eas_block_7871_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Final memory for bytecode block summary `eas_block_7871`. -/
def eas_block_7871_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 7871. -/
theorem eas_block_7871 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains x2 = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7871) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 x2 (eas_block_7871_stack (x1 := x1) (R := R)) (eas_block_7871_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((18) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7871⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7872⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7873⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7874⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7875⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7871_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains x2 = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7871) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 x2 (eas_block_7871_stack (x1 := x1) (R := R)) (eas_block_7871_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7871 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7876`. -/
def eas_block_7876_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x4 :: (UInt256.ofNat 7897) :: x8 :: x10 :: x0 :: x7 :: x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7876. -/
theorem eas_block_7876 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7876) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_7876_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata σ (k + 17) (C + ((54))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7876⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7877⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7878⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7879⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7880⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7881⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7882⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7883⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7884⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 7897) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7885⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7897), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7888⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7889⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7890⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7891⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7892⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 5725) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7893⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5725), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7896⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5725)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7876_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7876) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_7876_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7876 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7897_taken`. -/
def eas_block_7897_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)) :: (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)))) :: x7 :: x10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ((memLoad x0 mem) + (UInt256.ofNat 32)) :: x8 :: x9 :: (memLoad x0 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7897. -/
theorem eas_block_7897_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9744) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7897) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9744) (eas_block_7897_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem (M (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((59) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7897⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7898⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7899⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7900⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7902⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7903⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7904⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7905⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7914⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMload r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7915⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7916⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7917⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7918⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7919⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7920⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7921⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 9744) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7922⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9744), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7925⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9744)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7897_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9744) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7897) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9744) (eas_block_7897_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7897_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7897_fallthrough`. -/
def eas_block_7897_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)) :: (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)))) :: x7 :: x10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: ((memLoad x0 mem) + (UInt256.ofNat 32)) :: x8 :: x9 :: (memLoad x0 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7897. -/
theorem eas_block_7897_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7897) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7926) (eas_block_7897_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem (M (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((59) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) ((memLoad x0 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7897⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7898⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7899⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7900⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7902⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7903⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7904⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7905⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7914⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMload r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7915⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7916⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7917⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7918⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7919⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7920⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7921⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 9744) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7922⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9744), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7925⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7926)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7897_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (UInt256.land (memLoad ((memLoad x0 mem) + (UInt256.ofNat 32)) mem) (UInt256.ofNat 18446744073709551615)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7897) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7926) (eas_block_7897_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7897_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7926_taken`. -/
def eas_block_7926_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7926. -/
theorem eas_block_7926_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9702) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7926) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9702) (eas_block_7926_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7926⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7927⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 9702) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7928⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9702), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7931⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9702)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7926_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9702) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7926) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9702) (eas_block_7926_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7926_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7926_fallthrough`. -/
def eas_block_7926_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7926. -/
theorem eas_block_7926_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7926) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7932) (eas_block_7926_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7926⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7927⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 9702) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7928⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9702), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7931⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7932)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7926_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7926) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7932) (eas_block_7926_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7926_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7932_taken`. -/
def eas_block_7932_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) mem)) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7932. -/
theorem eas_block_7932_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9689) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9689) (eas_block_7932_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((31) + (memExpansionCost aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7932⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7934⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7935⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7936⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7937⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7938⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 9689) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7939⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9689), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7942⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9689)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7932_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9689) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9689) (eas_block_7932_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7932_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7932_fallthrough`. -/
def eas_block_7932_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) mem)) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7932. -/
theorem eas_block_7932_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) mem)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7943) (eas_block_7932_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((31) + (memExpansionCost aw (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7932⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7934⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7935⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7936⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7937⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7938⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 9689) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7939⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9689), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7942⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7943)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7932_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 64)) mem)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7932) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7943) (eas_block_7932_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7932_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7943_taken`. -/
def eas_block_7943_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7943. -/
theorem eas_block_7943_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9647) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7943) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9647) (eas_block_7943_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7943⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9647) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7944⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9647), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7947⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9647)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7943_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9647) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7943) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9647) (eas_block_7943_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7943_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7943_fallthrough`. -/
def eas_block_7943_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7943. -/
theorem eas_block_7943_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7943) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7948) (eas_block_7943_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7943⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9647) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7944⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9647), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7947⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7948)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7943_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7943) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7948) (eas_block_7943_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7943_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_7948`. -/
def eas_block_7948_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 8020) :: (memLoad (UInt256.ofNat 64) mem) :: x9 :: (UInt256.land (UInt256.ofNat 18446744073709551615) (memLoad x8 mem)) :: (memLoad (x11 + (UInt256.ofNat 96)) mem) :: (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (memLoad x11 mem)) :: (UInt256.isZero (UInt256.isZero (memLoad (x11 + (UInt256.ofNat 64)) mem))) :: (memLoad ((UInt256.ofNat 128) + x11) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: (memLoad (UInt256.ofNat 64) mem) :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7948. -/
theorem eas_block_7948 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4854) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7948) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4854) (eas_block_7948_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem (M (M (M (M (M (M aw (x11 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x8 (⟨32⟩ : UInt256)) x11 (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 128) + x11) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 36) (C + ((113) + (memExpansionCost aw (x11 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x11 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x8 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x11 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x8 (⟨32⟩ : UInt256)) x11 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x11 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x8 (⟨32⟩ : UInt256)) x11 (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x11 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x8 (⟨32⟩ : UInt256)) x11 (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 128) + x11) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x11 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) x8 (⟨32⟩ : UInt256)) x11 (⟨32⟩ : UInt256)) (x11 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 128) + x11) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7948⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7949⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7950⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7951⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7953⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7954⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMload r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7955⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7956⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMload r8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7957⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7958⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7967⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7968⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7969⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMload r13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7970⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7971⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7992⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7993⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7994⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7996⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7997⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genMload r20 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7998⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨7999⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8000⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8001⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8002⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8004⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMload r26 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8005⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8006⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8007⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := RD.genMload r29 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8009⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8010⟩ : UInt256), UInt8.ofNat 157, .SWAP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup15 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8011⟩ : UInt256), UInt8.ofNat 142, .DUP15, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.push2 (UInt256.ofNat 8020) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8012⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8020), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8015⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.push2 (UInt256.ofNat 4854) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8016⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 4854), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8019⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4854)) r36 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_7948_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4854) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7948) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4854) (eas_block_7948_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_7948 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8020`. -/
def eas_block_8020_stack {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {x14 : UInt256} {x15 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R)

/-- Final memory for bytecode block summary `eas_block_8020`. -/
def eas_block_8020_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x14 : UInt256} {x15 : UInt256} : ByteArray :=
  (x6.toByteArray.write 0 (x5.toByteArray.write 0 ((UInt256.land x14 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 (x4.toByteArray.write 0 (x3.toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 (x2.toByteArray.write 0 ((UInt256.land (UInt256.ofNat 18446744073709551615) (UInt256.ofNat ee.header.timestamp)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 mem x0.toNat 32) ((UInt256.ofNat 32) + x0).toNat 32) (x15 + (UInt256.ofNat 64)).toNat 32) ((UInt256.ofNat 96) + x15).toNat 32) (x15 + (UInt256.ofNat 128)).toNat 32) (x15 + (UInt256.ofNat 160)).toNat 32) (x15 + (UInt256.ofNat 192)).toNat 32) (x15 + (UInt256.ofNat 224)).toNat 32) (x15 + (UInt256.ofNat 256)).toNat 32) (x15 + (UInt256.ofNat 288)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8020. -/
theorem eas_block_8020 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8020) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8110) (eas_block_8020_stack (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (x15 := x15) (R := R)) (eas_block_8020_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x14 := x14) (x15 := x15)) (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) rdata σ (k + 48) (C + ((141) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + x15) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x15 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8020⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8021⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8023⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8024⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8025⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8027⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8028⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8029⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.timestamp (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8030⟩ : UInt256), UInt8.ofNat 66, .TIMESTAMP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8031⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8040⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8041⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8043⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8044⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8045⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8046⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8048⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMstore r17 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8049⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8050⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8052⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8053⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8054⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8056⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genMstore r23 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8057⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8058⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.dup14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8060⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8061⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := RD.genMstore r27 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8062⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8063⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8065⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8066⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := RD.genMstore r31 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8067⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8068⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.dup11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8089⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8090⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 224) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8091⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.dup13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8093⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8094⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := RD.genMstore r38 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8095⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.push2 (UInt256.ofNat 256) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8096⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 256), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.dup12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8099⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8100⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := RD.genMstore r42 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8101⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 288) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8102⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 288), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.dup11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8105⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8106⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := RD.genMstore r46 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8107⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8108⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8110)) r48 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8020_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8020) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8110) (eas_block_8020_stack (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (x15 := x15) (R := R)) (eas_block_8020_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x14 := x14) (x15 := x15)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_8020 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8110`. -/
def eas_block_8110_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 84) :: (UInt256.land (UInt256.ofNat 115792089237316195423570985008687907853269984665561335876943319670319585689600) (UInt256.shiftLeft (memLoad (x9 + (UInt256.ofNat 224)) mem) (UInt256.ofNat 96))) :: (memLoad (x9 + (UInt256.ofNat 64)) mem) :: (memLoad (x9 + (UInt256.ofNat 96)) mem) :: (UInt256.isZero (UInt256.isZero (memLoad (x9 + (UInt256.ofNat 256)) mem))) :: (memLoad (x9 + (UInt256.ofNat 160)) mem) :: (memLoad ((UInt256.ofNat 288) + x9) mem) :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Final memory for bytecode block summary `eas_block_8110`. -/
def eas_block_8110_memory {mem : ByteArray} {x9 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.ofNat 115792089237316195423570985008687907853269984665561335876943319670319585689600) (UInt256.shiftLeft (memLoad (x9 + (UInt256.ofNat 192)) mem) (UInt256.ofNat 96))).toByteArray.write 0 ((memLoad (x9 + (UInt256.ofNat 32)) mem).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8110. -/
theorem eas_block_8110 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8110) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8254) (eas_block_8110_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (eas_block_8110_memory (mem := mem) (x9 := x9)) (M (M (M (M (M (M (M (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + x9) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((190) + (memExpansionCost aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + x9) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + x9) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + x9) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (x9 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x9 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + x9) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8110⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8111⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8113⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8114⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8115⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8116⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8118⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8119⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMload r8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8120⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 224) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8121⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8123⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8124⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMload r12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8125⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8126⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8127⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8129⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8130⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMload r17 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8131⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8132⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8133⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8135⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8136⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := RD.genMload r22 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8137⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 256) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8138⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 256), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8141⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8142⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMload r26 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8143⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8144⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8145⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8146⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8147⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8149⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8150⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := RD.genMload r33 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8151⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8152⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 288) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8153⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 288), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8156⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := RD.genMload r37 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8157⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8158⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8159⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := RD.genMload r40 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8161⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.swap7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8162⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.dup8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8163⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.swap7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8164⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8165⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.dup9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8167⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8168⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8169⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := r48.dup11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8170⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r50 := RD.genMstore r49 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8171⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8172⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r52 := r51.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8174⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r53 := r52.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665561335876943319670319585689600) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8175⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665561335876943319670319585689600), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r54 := r53.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8208⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8209⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r56 := r55.dup9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8211⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r57 := r56.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8212⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r58 := RD.genMstore r57 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8213⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8214⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r60 := r59.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8216⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r61 := r60.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665561335876943319670319585689600) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8217⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665561335876943319670319585689600), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r62 := r61.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8250⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r63 := r62.push1 (UInt256.ofNat 84) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8251⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 84), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r64 := r63.dup8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8253⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8254)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8110_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8110) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8254) (eas_block_8110_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (eas_block_8110_memory (mem := mem) (x9 := x9)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_8110 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8254`. -/
def eas_block_8254_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x7) :: (x8 + (UInt256.ofNat 153)) :: (memLoad x7 (x6.toByteArray.write 0 ((UInt256.shiftLeft x5 (UInt256.ofNat 248)).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (UInt256.shiftLeft x4 (UInt256.ofNat 192))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (UInt256.shiftLeft x3 (UInt256.ofNat 192))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x8 + (UInt256.ofNat 104)).toNat 32) (x8 + (UInt256.ofNat 112)).toNat 32) (x8 + (UInt256.ofNat 120)).toNat 32) (x8 + (UInt256.ofNat 121)).toNat 32)) :: (UInt256.ofNat 8374) :: (memLoad x7 (x6.toByteArray.write 0 ((UInt256.shiftLeft x5 (UInt256.ofNat 248)).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (UInt256.shiftLeft x4 (UInt256.ofNat 192))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (UInt256.shiftLeft x3 (UInt256.ofNat 192))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x8 + (UInt256.ofNat 104)).toNat 32) (x8 + (UInt256.ofNat 112)).toNat 32) (x8 + (UInt256.ofNat 120)).toNat 32) (x8 + (UInt256.ofNat 121)).toNat 32)) :: x8 :: R)

/-- Final memory for bytecode block summary `eas_block_8254`. -/
def eas_block_8254_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x8 : UInt256} : ByteArray :=
  (x6.toByteArray.write 0 ((UInt256.shiftLeft x5 (UInt256.ofNat 248)).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (UInt256.shiftLeft x4 (UInt256.ofNat 192))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (UInt256.shiftLeft x3 (UInt256.ofNat 192))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x8 + (UInt256.ofNat 104)).toNat 32) (x8 + (UInt256.ofNat 112)).toNat 32) (x8 + (UInt256.ofNat 120)).toNat 32) (x8 + (UInt256.ofNat 121)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8254. -/
theorem eas_block_8254 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4400) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8254) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4400) (eas_block_8254_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (eas_block_8254_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x8 := x8)) (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 104)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 112)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 120)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 121)) (⟨32⟩ : UInt256)) x7 (⟨32⟩ : UInt256)) rdata σ (k + 43) (C + ((134) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 104)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 104)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 112)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 104)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 112)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 120)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 104)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 112)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 120)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 121)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 104)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 112)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 120)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 121)) (⟨32⟩ : UInt256)) x7 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8254⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8255⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8256⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8258⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8259⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8292⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 104) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8293⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 104), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8295⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8296⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8297⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8298⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8300⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8301⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8334⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 112) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8335⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 112), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8337⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8338⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMstore r17 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8339⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 248) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8340⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 248), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8342⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 120) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8343⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 120), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8345⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8346⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genMstore r23 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8347⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 121) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8348⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 121), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8350⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8351⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := RD.genMstore r27 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8352⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8353⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := RD.genMload r29 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8354⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8355⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8356⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 153) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8357⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 153), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8359⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8360⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8361⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8362⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8364⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8365⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.push2 (UInt256.ofNat 8374) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8366⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8374), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := r40.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8369⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.push2 (UInt256.ofNat 4400) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8370⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 4400), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8373⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4400)) r43 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8254_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4400) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8254) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4400) (eas_block_8254_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (eas_block_8254_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_8254 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8374`. -/
def eas_block_8374_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: ((UInt256.ofNat 4) + ((UInt256.ofNat 153) + (UInt256.sub (x1 + x0) x1))) :: (UInt256.ofNat 8473) :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `eas_block_8374`. -/
def eas_block_8374_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} : ByteArray :=
  ((((UInt256.ofNat 153) + (UInt256.sub (x1 + x0) x1)) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639908)).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 115792089210356248756420345214020892766250353992003419616917011526809519390720) (UInt256.shiftLeft x4 (UInt256.ofNat 224))).toByteArray.write 0 mem ((x1 + x0) + (UInt256.ofNat 153)).toNat 32) x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8374. -/
theorem eas_block_8374 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4883) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8374) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4883) (eas_block_8374_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (eas_block_8374_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) (M (M aw ((x1 + x0) + (UInt256.ofNat 153)) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) rdata σ (k + 27) (C + ((84) + (memExpansionCost aw ((x1 + x0) + (UInt256.ofNat 153)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((x1 + x0) + (UInt256.ofNat 153)) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8374⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8375⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8376⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8377⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 224) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8378⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8380⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 115792089210356248756420345214020892766250353992003419616917011526809519390720) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8381⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089210356248756420345214020892766250353992003419616917011526809519390720), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8414⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 153) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8415⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 153), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8417⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8418⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8419⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.sub (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8420⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 153) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8421⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 153), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8423⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639908) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8424⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639908), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8457⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8458⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8459⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8460⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8461⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8463⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 8473) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8464⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8473), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8467⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8468⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 4883) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8469⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 4883), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8472⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4883)) r27 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8374_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4883) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8374) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4883) (eas_block_8374_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (eas_block_8374_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_8374 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8473_taken`. -/
def eas_block_8473_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((keccakWord x1 (memLoad x0 mem) mem) :: R)

/-- Final memory for bytecode block summary `eas_block_8473_taken`. -/
def eas_block_8473_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8473. -/
theorem eas_block_8473_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 8511) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8511) (eas_block_8473_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (eas_block_8473_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8473⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8474⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8475⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8476⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8477⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8478⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8480⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8481⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8483⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8485⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8486⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8488⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8490⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8491⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8492⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 8511) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8493⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8511), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8496⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8511)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8473_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 8511) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8511) (eas_block_8473_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (eas_block_8473_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := eas_block_8473_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8473_fallthrough`. -/
def eas_block_8473_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((keccakWord x1 (memLoad x0 mem) mem) :: R)

/-- Final memory for bytecode block summary `eas_block_8473_fallthrough`. -/
def eas_block_8473_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8473. -/
theorem eas_block_8473_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8497) (eas_block_8473_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (eas_block_8473_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8473⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8474⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8475⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8476⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8477⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8478⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8480⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8481⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8483⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8485⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8486⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8488⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8490⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8491⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8492⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 8511) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8493⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8511), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8496⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8497)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8473_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((keccakWord x1 (memLoad x0 mem) mem).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8497) (eas_block_8473_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (eas_block_8473_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := eas_block_8473_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8497`. -/
def eas_block_8497_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 4294967295) ((UInt256.ofNat 1) + x1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8497. -/
theorem eas_block_8497 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 8110) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8497) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8110) (eas_block_8497_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8497⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8498⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8500⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push4 (UInt256.ofNat 4294967295) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8501⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 4294967295), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8506⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8110) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8507⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8110), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8510⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8110)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8497_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 8110) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8497) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8110) (eas_block_8497_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_8497 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_8511`. -/
def eas_block_8511_stack {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {x14 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x10 + (UInt256.ofNat 96)) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) :: ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) :: (UInt256.ofNat 8775) :: (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) :: x13 :: x0 :: x12 :: x10 :: x6 :: x9 :: x11 :: x2 :: x3 :: x14 :: x7 :: x4 :: x5 :: x8 :: R)

/-- Final memory for bytecode block summary `eas_block_8511`. -/
def eas_block_8511_memory {mem : ByteArray} {x0 : UInt256} {x10 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8511. -/
theorem eas_block_8511 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 21 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8511) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8627) (eas_block_8511_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (R := R)) (eas_block_8511_memory (mem := mem) (x0 := x0) (x10 := x10)) (M (M (M (M (M (M (M (M aw x10 (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) x10 (⟨32⟩ : UInt256)) (x10 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x10 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x10 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (memLoad x10 ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (memLoad (x10 + (UInt256.ofNat 32)) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (memLoad x10 ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (memLoad (x10 + (UInt256.ofNat 32)) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320)) (UInt256.land (UInt256.land (memLoad (x10 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 18446744073709551615)) (UInt256.ofNat 18446744073709551615)))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8511⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8512⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8513⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap14 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8514⟩ : UInt256), UInt8.ofNat 157, .SWAP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8515⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8516⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8517⟩ : UInt256), UInt8.ofNat 155, .SWAP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8518⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8519⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8520⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8521⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8522⟩ : UInt256), UInt8.ofNat 156, .SWAP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8523⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8524⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8525⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8526⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8527⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8528⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8529⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8530⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8531⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8532⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := RD.genMstore r22 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8534⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8535⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8537⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := RD.genMstore r25 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8539⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8540⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8542⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := RD.genKeccak256 r28 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8544⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8545⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := RD.genMload r30 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8546⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8547⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r33⟩ := RD.sstore r32 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8548⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8549⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.dup6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8551⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8552⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := RD.genMload r36 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8553⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8554⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8556⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8557⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r41⟩ := RD.sstore r40 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8558⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.push2 (UInt256.ofNat 8775) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8559⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8775), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8562⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8564⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := r44.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8565⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8566⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8575⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8576⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := r48.dup10 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8578⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r50 := r49.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8579⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r51 := RD.genMload r50 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8580⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r52 := r51.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8581⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r53 := r52.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8582⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r54 := r53.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8583⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r55 := r54.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8616⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r56⟩ := RD.sload r55 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8617⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r57 := r56.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8618⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r58 := r57.or (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8619⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r59 := r58.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8620⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r60⟩ := RD.sstore r59 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8621⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r61 := r60.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8622⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r62 := r61.dup8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8624⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r63 := r62.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8625⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r64 := RD.genMload r63 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨8626⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8627)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_8511_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 21 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8511) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 8627) (eas_block_8511_stack (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (R := R)) (eas_block_8511_memory (mem := mem) (x0 := x0) (x10 := x10)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (memLoad x10 ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (memLoad (x10 + (UInt256.ofNat 32)) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (memLoad x10 ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (memLoad (x10 + (UInt256.ofNat 32)) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320)) (UInt256.land (UInt256.land (memLoad (x10 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 (x0.toByteArray.write 0 mem x10.toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 18446744073709551615)) (UInt256.ofNat 18446744073709551615)))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := eas_block_8511 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end easBlocks
