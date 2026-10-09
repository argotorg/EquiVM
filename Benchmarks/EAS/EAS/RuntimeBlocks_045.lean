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

/-- Automatically generated RD summary for bytecode block at pc 14755. -/
theorem eas_block_14755 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14755) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14755⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14756⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14758⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 7691213494486655955118957457057678164760521221358442927666071922997119156224) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14759⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 7691213494486655955118957457057678164760521221358442927666071922997119156224), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14792⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14793⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14794⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 14795. -/
theorem eas_block_14795 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14795) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14795⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14796⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14798⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 9705249165870277706060011232374481614032455581601064421615209634208084393984) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14799⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 9705249165870277706060011232374481614032455581601064421615209634208084393984), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14832⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14833⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14834⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `eas_block_14835`. -/
def eas_block_14835_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((33) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x6 :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 4) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 32) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `eas_block_14835`. -/
def eas_block_14835_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 93301673981065310694808778836234761291861610861423810446997967148136928378880).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 14835. -/
theorem eas_block_14835 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14835) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14883) (eas_block_14835_stack (g := g) (mem := mem) (aw := aw) (C := C) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (eas_block_14835_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((35) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14835⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14836⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14837⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14839⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 93301673981065310694808778836234761291861610861423810446997967148136928378880) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14840⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 93301673981065310694808778836234761291861610861423810446997967148136928378880), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14873⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14874⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14875⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14877⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14878⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14880⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup11 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14881⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genGas (RD.normalizeCounters (k' := k + 12) (C' := C + ((33) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) r12 (by omega) (by omega)) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14882⟩ : UInt256), UInt8.ofNat 90, .GAS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14883)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14835_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14835) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14883) (eas_block_14835_stack (g := g) (mem := mem) (aw := aw) (C := C) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (eas_block_14835_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14835 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 14883: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 14884 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `eas_block_14884_taken`. -/
def eas_block_14884_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14884. -/
theorem eas_block_14884_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14965) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14884) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14965) (eas_block_14884_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14884⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14885⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14886⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14965) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14887⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14965), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14890⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14965)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14884_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14965) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14884) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14965) (eas_block_14884_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14884_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14884_fallthrough`. -/
def eas_block_14884_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14884. -/
theorem eas_block_14884_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14884) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14891) (eas_block_14884_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14884⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14885⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14886⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14965) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14887⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14965), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14890⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14891)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14884_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14884) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14891) (eas_block_14884_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14884_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14891_taken`. -/
def eas_block_14891_taken_stack {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x5 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14891. -/
theorem eas_block_14891_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14904) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14891) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14904) (eas_block_14891_taken_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14891⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14892⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14904) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14893⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14904), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14896⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14904)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14891_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14904) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14891) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14904) (eas_block_14891_taken_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14891_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14891_fallthrough`. -/
def eas_block_14891_fallthrough_stack {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x5 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14891. -/
theorem eas_block_14891_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14891) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14897) (eas_block_14891_fallthrough_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14891⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14892⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14904) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14893⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14904), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14896⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14897)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14891_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14891) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14897) (eas_block_14891_fallthrough_stack (x0 := x0) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14891_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14897`. -/
def eas_block_14897_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14897. -/
theorem eas_block_14897 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14728) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14897) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14728) (eas_block_14897_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14897⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14898⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14899⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14728) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14900⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14728), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14903⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14728)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14897_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14728) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14897) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14728) (eas_block_14897_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14897 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14904_taken`. -/
def eas_block_14904_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 32) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14904. -/
theorem eas_block_14904_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14957) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14904) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14957) (eas_block_14904_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14904⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14905⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14906⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14907⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14909⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.returndatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14910⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14911⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.gt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14912⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 14957) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14913⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14957), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14916⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14957)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14904_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14957) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14904) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14957) (eas_block_14904_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14904_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14904_fallthrough`. -/
def eas_block_14904_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 32) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14904. -/
theorem eas_block_14904_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14904) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14917) (eas_block_14904_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14904⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14905⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14906⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14907⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14909⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.returndatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14910⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14911⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.gt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14912⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 14957) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14913⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14957), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14916⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14917)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14904_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14904) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14917) (eas_block_14904_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14904_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14917`. -/
def eas_block_14917_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (UInt256.ofNat 14930) :: x1 :: x0 :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14917. -/
theorem eas_block_14917 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4883) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14917) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4883) (eas_block_14917_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14917⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14918⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14930) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14919⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14930), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14922⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14924⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup4 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14925⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 4883) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14926⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 4883), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14929⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4883)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14917_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 4883) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14917) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 4883) (eas_block_14917_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14917 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14930_taken`. -/
def eas_block_14930_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14930. -/
theorem eas_block_14930_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14953) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14930) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14953) (eas_block_14930_taken_stack (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14930⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14931⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14932⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.sub (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14933⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.slt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14934⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14953) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14935⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14953), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14938⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14953)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14930_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14953) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14930) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14953) (eas_block_14930_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14930_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14930_fallthrough`. -/
def eas_block_14930_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 14930. -/
theorem eas_block_14930_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14930) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14939) (eas_block_14930_fallthrough_stack (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14930⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14931⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14932⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.sub (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14933⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.slt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14934⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14953) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14935⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14953), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14938⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14939)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14930_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14930) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14939) (eas_block_14930_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14930_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14939`. -/
def eas_block_14939_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 14947) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14939. -/
theorem eas_block_14939 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 7319) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14939) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7319) (eas_block_14939_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 14947) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14939⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14947), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14942⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7319) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14943⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7319), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14946⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7319)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14939_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 7319) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14939) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 7319) (eas_block_14939_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14939 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `eas_block_14947`. -/
def eas_block_14947_stack {immWords : String → UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords).size) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14947. -/
theorem eas_block_14947 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14897) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14947) R mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14897) (eas_block_14947_stack (immWords := immWords) (R := R)) mem aw rdata σ (k + 4) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14947⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.codesize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14948⟩ : UInt256), UInt8.ofNat 56, .CODESIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 14897) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14949⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14897), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14952⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14897)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14947_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14897) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14947) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14897) (eas_block_14947_stack (immWords := immWords) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14947 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14953. -/
theorem eas_block_14953 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14953) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14953⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14954⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14955⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14956⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `eas_block_14957`. -/
def eas_block_14957_stack {rdata : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat rdata.size) :: R)

/-- Automatically generated RD summary for bytecode block at pc 14957. -/
theorem eas_block_14957 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14917) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14957) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14917) (eas_block_14957_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14957⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.returndatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14958⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14959⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14960⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14917) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14961⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14917), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14964⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14917)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14957_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14917) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14957) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14917) (eas_block_14957_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14957 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14965. -/
theorem eas_block_14965 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hguard0 : x5.toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14965) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14965⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14966⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14968⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.returndatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14969⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup8 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14970⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14971⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genReturndatacopy r6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14972⟩ : UInt256), UInt8.ofNat 62, .RETURNDATACOPY, none, immutableLayout_inBounds, immutableTemplate_size64)) hguard0 (by evm_ov)
  have r8 := r7.returndatasize (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14973⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14974⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r9 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14975⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `eas_block_14976`. -/
def eas_block_14976_stack {x0 : UInt256} {x3 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x6 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 14976. -/
theorem eas_block_14976 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14976) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14985) (eas_block_14976_stack (x0 := x0) (x3 := x3) (x6 := x6) (R := R)) mem aw rdata σ (k + 9) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14976⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap6 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14977⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap5 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14978⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14979⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14980⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14981⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14982⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.pop (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14983⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14984⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14985)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14976_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14976) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14985) (eas_block_14976_stack (x0 := x0) (x3 := x3) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14976 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 14985. -/
theorem eas_block_14985_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14998) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14985) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14998) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14985⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14986⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14987⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.lt (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14988⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14998) (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14989⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14998), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jumpiT (by immutable_decode(Benchmarks.EAS.EAS.immutableLayout, Benchmarks.EAS.EAS.easBytecode, immWords, (⟨14992⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14998)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem eas_block_14985_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lt x0 x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) 0).contains (UInt256.ofNat 14998) = true)
    (h : RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14985) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.EAS.EAS.immutableLayout.runtime Benchmarks.EAS.EAS.easBytecode immWords) ee g s0 (UInt256.ofNat 14998) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (eas_block_14985_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end easBlocks
