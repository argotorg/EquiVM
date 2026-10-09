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

/-- Final stack for bytecode block summary `eas_block_11367_fallthrough`. -/
def eas_block_11367_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x0 + (UInt256.ofNat 96)) mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11367. -/
theorem eas_block_11367_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (x0 + (UInt256.ofNat 96)) mem) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11367) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11378) (eas_block_11367_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((29) + (memExpansionCost aw (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11367⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11368⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11370⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11371⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11372⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11373⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11538) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11374⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11538), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11377⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11378)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11367_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (x0 + (UInt256.ofNat 96)) mem) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11367) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11378) (eas_block_11367_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11367_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11378`. -/
def eas_block_11378_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x8 :: x4 :: (UInt256.ofNat 11414) :: x5 :: x1 :: (UInt256.ofNat 1461501637330902918203684832716283019655932542975) :: x2 :: x3 :: x4 :: (UInt256.ofNat 1) :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11378. -/
theorem eas_block_11378 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11378) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11378_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 11) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11378⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11379⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11380⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11401⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11402⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11404⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11414) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11405⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11414), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11408⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11409⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 5725) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11410⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5725), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11413⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5725)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11378_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11378) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11378_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11378 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11414`. -/
def eas_block_11414_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x10 :: x6 :: (UInt256.ofNat 11425) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `eas_block_11414`. -/
def eas_block_11414_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11414. -/
theorem eas_block_11414 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11414) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11414_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (eas_block_11414_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11414⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11415⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 11425) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11416⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11425), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11419⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11420⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5725) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11421⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5725), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11424⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5725)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11414_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11414) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11414_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (eas_block_11414_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11414 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11425`. -/
def eas_block_11425_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x10 :: x5 :: (UInt256.ofNat 11441) :: (memLoad (x1 + (UInt256.ofNat 160)) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11425. -/
theorem eas_block_11425 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11425) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11425_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem (M aw (x1 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((35) + (memExpansionCost aw (x1 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11425⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11426⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11427⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11429⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11430⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11431⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11441) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11432⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11441), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11435⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11436⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 5725) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11437⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5725), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11440⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5725)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11425_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11425) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11425_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11425 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11441`. -/
def eas_block_11441_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad (UInt256.ofNat 128) (x1.toByteArray.write 0 mem x0.toNat 32)) + (UInt256.ofNat 32)) (x1.toByteArray.write 0 mem x0.toNat 32)) :: x6 :: (UInt256.ofNat 11459) :: x4 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `eas_block_11441`. -/
def eas_block_11441_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11441. -/
theorem eas_block_11441 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11441) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11441_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (eas_block_11441_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 128) (x1.toByteArray.write 0 mem x0.toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 128) (x1.toByteArray.write 0 mem x0.toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11441⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11442⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11443⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11459) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11444⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11459), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11447⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11448⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11450⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMload r7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11452⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11453⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMload r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11454⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 5725) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11455⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5725), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11458⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5725)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11441_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 5725) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11441) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 5725) (eas_block_11441_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (eas_block_11441_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11441 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11459`. -/
def eas_block_11459_stack {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {x14 : UInt256} {x15 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x8 :: x15 :: x10 :: x11 :: x12 :: x13 :: x14 :: (x6 + x7) :: R)

/-- Final memory for bytecode block summary `eas_block_11459`. -/
def eas_block_11459_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x4 : UInt256} : ByteArray :=
  (x4.toByteArray.write 0 (x1.toByteArray.write 0 mem x0.toNat 32) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 mem x0.toNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11459. -/
theorem eas_block_11459 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 10064) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11459) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 10064) (eas_block_11459_stack (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (x15 := x15) (R := R)) (eas_block_11459_memory (mem := mem) (x0 := x0) (x1 := x1) (x4 := x4)) (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 mem x0.toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 32)) rdata σ (k + 22) (C + ((66) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 mem x0.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 mem x0.toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 mem x0.toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 32)) + (375 + 8 * (UInt256.ofNat 32).toNat + 4 * 375))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11459⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11460⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11461⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11462⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11463⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11465⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11466⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11467⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11468⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 63303341723853913981516773384969502377504159846791835706605975315714145524533) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11469⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 63303341723853913981516773384969502377504159846791835706605975315714145524533), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11502⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11504⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11525⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMload r13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11527⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11528⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11529⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genLog4 r16 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11530⟩ : UInt256), UInt8.ofNat 164, .LOG4, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r18 := r17.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11531⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11532⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11533⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 10064) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11534⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 10064), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11537⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10064)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11459_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 10064) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11459) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 10064) (eas_block_11459_stack (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (x15 := x15) (R := R)) (eas_block_11459_memory (mem := mem) (x0 := x0) (x1 := x1) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11459 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11538`. -/
def eas_block_11538_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) :: x2 :: x1 :: R)

/-- Final memory for bytecode block summary `eas_block_11538`. -/
def eas_block_11538_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11538. -/
theorem eas_block_11538 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11563) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11538) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11563) (eas_block_11538_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (eas_block_11538_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11538⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11563) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11539⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11563), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11542⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11543⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11544⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11545⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11547⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11548⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11550⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMstore r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11552⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11553⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11555⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11557⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11558⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11559⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11560⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11561⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11562⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11563)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11538_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11563) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11538) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11563) (eas_block_11538_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (eas_block_11538_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := eas_block_11538 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11563_taken`. -/
def eas_block_11563_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11563. -/
theorem eas_block_11563_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9302) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11563) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9302) (eas_block_11563_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11563⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11564⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 9302) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11565⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9302), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11568⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9302)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11563_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 9302) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11563) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 9302) (eas_block_11563_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11563_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11563_fallthrough`. -/
def eas_block_11563_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11563. -/
theorem eas_block_11563_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11563) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11569) (eas_block_11563_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11563⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11564⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 9302) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11565⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9302), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11568⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11569)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11563_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11563) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11569) (eas_block_11563_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11563_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11569`. -/
def eas_block_11569_stack {immWords : String → UInt256} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size) :: x1 :: x0 :: x4 :: x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11569. -/
theorem eas_block_11569 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11378) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11569) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11378) (eas_block_11569_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11569⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11570⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.codesize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11571⟩ : UInt256), UInt8.ofNat 56, .CODESIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11378) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11572⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11378), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11575⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11378)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11569_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11378) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11569) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11378) (eas_block_11569_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11569 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11576`. -/
def eas_block_11576_stack {immWords : String → UInt256} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size) :: (UInt256.ofNat (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size) :: (memLoad (x0 + x1) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11576. -/
theorem eas_block_11576 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11316) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11576) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11316) (eas_block_11576_stack (immWords := immWords) (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw (x0 + x1) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((28) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11576⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11577⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11578⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11579⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11580⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.codesize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11581⟩ : UInt256), UInt8.ofNat 56, .CODESIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11582⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 11316) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11583⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11316), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11586⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11316)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11576_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11316) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11576) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11316) (eas_block_11576_stack (immWords := immWords) (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11576 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11587`. -/
def eas_block_11587_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: (keccakWord (UInt256.ofNat 0) x1 ((x3 + (UInt256.ofNat 6)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)) :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `eas_block_11587`. -/
def eas_block_11587_memory {mem : ByteArray} {x3 : UInt256} : ByteArray :=
  ((x3 + (UInt256.ofNat 6)).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11587. -/
theorem eas_block_11587 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11587) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (eas_block_11587_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (eas_block_11587_memory (mem := mem) (x3 := x3)) (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) x1) rdata σ (k + 12) (C + ((31) + (memExpansionCost aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) x1) + (30 + 6 * ((x1.toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11587⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11588⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 6) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11589⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11591⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11592⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11593⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11595⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11596⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11597⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11599⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11600⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11601⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11603)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11587_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11587) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (eas_block_11587_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (eas_block_11587_memory (mem := mem) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11587 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11603. -/
theorem eas_block_11603_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11764) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11764) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11603⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11604⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11637⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11638⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11639⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.lt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11640⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11764) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11641⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11764), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11644⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11764)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11603_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11764) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11764) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11603_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11603. -/
theorem eas_block_11603_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11645) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11603⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11604⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11637⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11638⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11639⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.lt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11640⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11764) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11641⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11764), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11644⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11645)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11603_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11645) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11603_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11645_taken`. -/
def eas_block_11645_taken_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: (UInt256.ofNat 1) :: (UInt256.ofNat 6) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11645. -/
theorem eas_block_11645_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904)) x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11709) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11645) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11709) (eas_block_11645_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 14) (C + ((48))) := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11645⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11646⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11647⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11648⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11649⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11651⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11652⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11653⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 6) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11686⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11688⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11689⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.lt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11690⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 11709) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11691⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11694⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11709)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11645_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904)) x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11709) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11645) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11709) (eas_block_11645_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11645_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11645_fallthrough`. -/
def eas_block_11645_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: x4 :: (UInt256.ofNat 1) :: (UInt256.ofNat 6) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11645. -/
theorem eas_block_11645_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904)) x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11645) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11695) (eas_block_11645_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 14) (C + ((48))) := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11645⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11646⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11647⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11648⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11649⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11651⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11652⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11653⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 6) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11686⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11688⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11689⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.lt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11690⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 11709) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11691⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11709), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11694⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11695)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11645_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.land x4 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904)) x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11645) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11695) (eas_block_11645_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11645_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11695`. -/
def eas_block_11695_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 11695. -/
theorem eas_block_11695 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11367) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11695) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11367) (eas_block_11695_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (x6 + x5) ((UInt256.shiftLeft x3 x4) + x4)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11695⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11696⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11697⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11698⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11699⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11700⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11701⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11702⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11703⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sstore r9 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11704⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 11367) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11705⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11367), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11708⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11367)) r12 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11695_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11367) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11695) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11367) (eas_block_11695_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (x6 + x5) ((UInt256.shiftLeft x3 x4) + x4)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := eas_block_11695 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11709`. -/
def eas_block_11709_stack {immWords : String → UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size) :: (UInt256.ofNat (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size) :: (UInt256.ofNat (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size) :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11709. -/
theorem eas_block_11709 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11695) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11709) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11695) (eas_block_11709_stack (immWords := immWords) (x3 := x3) (R := R)) mem (M aw (x0 + x1) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.land (UInt256.shiftLeft x3 (UInt256.ofNat 3)) (UInt256.ofNat 248)))) (memLoad (x0 + x1) mem))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11709⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11710⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11711⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11712⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 248) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11745⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 248), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11747⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11748⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11750⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11751⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shr (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11752⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.not (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11753⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11754⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11755⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11756⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.codesize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11757⟩ : UInt256), UInt8.ofNat 56, .CODESIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11758⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11759⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 11695) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11760⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11695), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11763⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11695)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11709_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11695) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11709) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11695) (eas_block_11709_stack (immWords := immWords) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.land (UInt256.shiftLeft x3 (UInt256.ofNat 3)) (UInt256.ofNat 248)))) (memLoad (x0 + x1) mem))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := eas_block_11709 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11764`. -/
def eas_block_11764_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: x1 :: ((UInt256.ofNat 32) + x2) :: (x3 + (UInt256.ofNat 1)) :: x4 :: x5 :: x6 :: x7 :: x11 :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11764. -/
theorem eas_block_11764 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11603) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11764) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (eas_block_11764_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem (M aw (x2 + x1) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 (memLoad (x2 + x1) mem)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11764⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11765⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11766⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11767⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11768⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11769⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sstore r6 hperm (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11770⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup12 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11771⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11772⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11773⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11774⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11776⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11777⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11778⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11779⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11780⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11782⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11783⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11784⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11785⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11786⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 11603) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11787⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11603), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11790⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11603)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11764_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11603) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11764) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11603) (eas_block_11764_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 (memLoad (x2 + x1) mem)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := eas_block_11764 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_11791_taken`. -/
def eas_block_11791_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11791. -/
theorem eas_block_11791_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11818) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11791) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11818) (eas_block_11791_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11791⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11792⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11793⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11794⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11795⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11796⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11797⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap7 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11798⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11799⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11800⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.gt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11801⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 11818) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11802⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11818), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨11805⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11818)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_11791_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.gt x0 x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 11818) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11791) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 11818) (eas_block_11791_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_11791_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end easBlocks
