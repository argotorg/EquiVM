import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.Morpho.MorphoBlue.Bytecode
import Benchmarks.Morpho.MorphoBlue.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace morphoBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.Morpho.MorphoBlue.immutableLayout.sites = [(6282, 32, "DOMAIN_SEPARATOR"), (9401, 32, "DOMAIN_SEPARATOR")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.Morpho.MorphoBlue.immutableLayout.inBounds Benchmarks.Morpho.MorphoBlue.morphoBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.Morpho.MorphoBlue.morphoBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords).size = Benchmarks.Morpho.MorphoBlue.morphoBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `morpho_block_8415`. -/
def morpho_block_8415_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.xor x6 (UInt256.isZero x13)) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8415. -/
theorem morpho_block_8415 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8415) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8415_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8415⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup14 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8416⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8417⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8418⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.xor (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8419⟩ : UInt256), UInt8.ofNat 24, .XOR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12097) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8420⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12097), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8423⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12097)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8415_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8415) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8415_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8415 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8424`. -/
def morpho_block_8424_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 8461) :: (UInt256.ofNat 8469) :: x4 :: x6 :: x0 :: x1 :: x2 :: x3 :: (UInt256.land x7 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: x5 :: (UInt256.ofNat 1461501637330902918203684832716283019655932542975) :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8424. -/
theorem morpho_block_8424 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12594) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8424) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12594) (morpho_block_8424_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 11) (C + ((36))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8424⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8425⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap7 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8446⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8447⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup10 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8448⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8449⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8450⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8469) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8451⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8469), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 8461) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8454⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8461), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 12594) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8457⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12594), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8460⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12594)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8424_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12594) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8424) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12594) (morpho_block_8424_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8424 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8461`. -/
def morpho_block_8461_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero x8)) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8461. -/
theorem morpho_block_8461 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8461) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8461_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8461⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8462⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8463⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.iszero (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8464⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12097) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8465⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12097), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8468⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12097)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8461_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8461) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8461_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8461 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8469`. -/
def morpho_block_8469_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: (UInt256.ofNat 5612) :: (UInt256.ofNat 8481) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8469. -/
theorem morpho_block_8469 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 13096) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8469) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 13096) (morpho_block_8469_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8469⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8481) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8470⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8481), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 5612) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8473⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5612), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8476⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 13096) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8477⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13096), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8480⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13096)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8469_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 13096) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8469) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 13096) (morpho_block_8469_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8469 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8481`. -/
def morpho_block_8481_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x7 :: x4 :: (UInt256.ofNat 8491) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8481. -/
theorem morpho_block_8481 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 13166) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8481) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 13166) (morpho_block_8481_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8481⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8491) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8482⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8491), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8485⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup10 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8486⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 13166) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8487⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13166), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8490⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13166)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8481_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 13166) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8481) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 13166) (morpho_block_8481_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8481 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8491_taken`. -/
def morpho_block_8491_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8491. -/
theorem morpho_block_8491_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 8934) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8491) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8934) (morpho_block_8491_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8491⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8934) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8492⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8934), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8495⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8934)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8491_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 8934) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8491) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8934) (morpho_block_8491_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8491_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8491_fallthrough`. -/
def morpho_block_8491_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8491. -/
theorem morpho_block_8491_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8491) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8496) (morpho_block_8491_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8491⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8934) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8492⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8934), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8495⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8496)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8491_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8491) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8496) (morpho_block_8491_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8491_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8496`. -/
def morpho_block_8496_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x11 :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x1 (UInt256.ofNat 64) (x10.toByteArray.write 0 (x3.toByteArray.write 0 mem x1.toNat 32) x9.toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) x2) :: (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x1 (UInt256.ofNat 64) (x10.toByteArray.write 0 (x3.toByteArray.write 0 mem x1.toNat 32) x9.toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) (UInt256.ofNat 128)) :: (UInt256.ofNat 8534) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x11 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `morpho_block_8496`. -/
def morpho_block_8496_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x9 : UInt256} {x10 : UInt256} : ByteArray :=
  (x10.toByteArray.write 0 (x3.toByteArray.write 0 mem x1.toNat 32) x9.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8496. -/
theorem morpho_block_8496 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15411) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8496) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15411) (morpho_block_8496_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (morpho_block_8496_memory (mem := mem) (x1 := x1) (x3 := x3) (x9 := x9) (x10 := x10)) (M (M (M aw x1 (⟨32⟩ : UInt256)) x9 (⟨32⟩ : UInt256)) x1 (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.pop (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8496⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8497⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap12 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8498⟩ : UInt256), UInt8.ofNat 155, .SWAP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8499⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8500⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8501⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap12 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8502⟩ : UInt256), UInt8.ofNat 155, .SWAP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8503⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap10 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8504⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8505⟩ : UInt256), UInt8.ofNat 154, .SWAP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap12 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8506⟩ : UInt256), UInt8.ofNat 155, .SWAP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8507⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8508⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8509⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8510⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 8534) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8511⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8534), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8514⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8516⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8518⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genKeccak256 r19 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8519⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8520⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8521⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8522⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8523⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8524⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.shr (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8526⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8527⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8528⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8529⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 15411) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8530⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15411), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8533⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15411)) r31 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8496_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15411) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8496) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15411) (morpho_block_8496_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (morpho_block_8496_memory (mem := mem) (x1 := x1) (x3 := x3) (x9 := x9) (x10 := x10)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8496 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8534`. -/
def morpho_block_8534_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: x11 :: x1 :: x2 :: x3 :: x0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8534. -/
theorem morpho_block_8534 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8534) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8538) (morpho_block_8534_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 4) (C + ((10))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8534⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8535⟩ : UInt256), UInt8.ofNat 154, .SWAP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup12 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8536⟩ : UInt256), UInt8.ofNat 139, .DUP12, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8537⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8538)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8534_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8534) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8538) (morpho_block_8534_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8534 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8538`. -/
def morpho_block_8538_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: (UInt256.ofNat 8547) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8538. -/
theorem morpho_block_8538 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15480) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8538) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15480) (morpho_block_8538_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8538⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8547) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8539⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8547), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup7 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8542⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 15480) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8543⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15480), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8546⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15480)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8538_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15480) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8538) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15480) (morpho_block_8538_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8538 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8547`. -/
def morpho_block_8547_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 1) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((keccakWord x3 (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32)).toByteArray.write 0 ((UInt256.land x1 x9).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32) (UInt256.ofNat 0).toNat 32) x12.toNat 32))) (⟨0⟩ : UInt256))) x4) :: x0 :: (UInt256.ofNat 8596) :: x4 :: ((UInt256.ofNat 1) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((keccakWord x3 (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32)).toByteArray.write 0 ((UInt256.land x1 x9).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32) (UInt256.ofNat 0).toNat 32) x12.toNat 32))) :: x6 :: x2 :: x12 :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 1) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((keccakWord x3 (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32)).toByteArray.write 0 ((UInt256.land x1 x9).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32) (UInt256.ofNat 0).toNat 32) x12.toNat 32))) (⟨0⟩ : UInt256))) :: x1 :: x2 :: x3 :: x4 :: x5 :: (UInt256.land x1 x9) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Final memory for bytecode block summary `morpho_block_8547`. -/
def morpho_block_8547_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x5 : UInt256} {x9 : UInt256} {x12 : UInt256} : ByteArray :=
  ((keccakWord x3 (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32)).toByteArray.write 0 ((UInt256.land x1 x9).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 (x5.toByteArray.write 0 mem x3.toNat 32) x12.toNat 32) (UInt256.ofNat 0).toNat 32) x12.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8547. -/
theorem morpho_block_8547 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12664) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8547) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12664) (morpho_block_8547_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (morpho_block_8547_memory (mem := mem) (x1 := x1) (x3 := x3) (x5 := x5) (x9 := x9) (x12 := x12)) (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x12 (⟨32⟩ : UInt256)) x3 (UInt256.ofNat 64)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) x12 (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8547⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8548⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8549⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8550⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8551⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup14 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8553⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8554⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup13 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8555⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8556⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8557⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup7 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8559⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8560⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8561⟩ : UInt256), UInt8.ofNat 152, .SWAP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup13 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8562⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8563⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8564⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap10 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8565⟩ : UInt256), UInt8.ofNat 153, .SWAP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8566⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8567⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8569⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8570⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := RD.genMstore r21 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8571⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8572⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8574⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := RD.genKeccak256 r24 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8576⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8577⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8579⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.dup9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8580⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8581⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r30⟩ := RD.sload r29 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8582⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8583⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8584⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := r32.dup8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8585⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8586⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8587⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 8596) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8588⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8596), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8591⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.push2 (UInt256.ofNat 12664) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8592⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12664), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8595⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12664)) r39 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8547_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12664) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8547) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12664) (morpho_block_8547_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (morpho_block_8547_memory (mem := mem) (x1 := x1) (x3 := x3) (x5 := x5) (x9 := x9) (x12 := x12)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8547 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8596`. -/
def morpho_block_8596_stack {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.ofNat 8645) :: x4 :: x5 :: (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8596. -/
theorem morpho_block_8596 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15480) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8596) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15480) (morpho_block_8596_stack (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land x6 (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8596⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8597⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8598⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8631⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap7 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8632⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8633⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8634⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8635⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sstore r8 hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8636⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 8645) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8637⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8645), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8640⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 15480) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8641⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15480), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8644⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15480)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8596_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15480) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8596) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15480) (morpho_block_8596_stack (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land x6 (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land x0 x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8596 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8645`. -/
def morpho_block_8645_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 1) + (keccakWord x6 (UInt256.ofNat 64) (x1.toByteArray.write 0 (x8.toByteArray.write 0 mem x6.toNat 32) x2.toNat 32))) (⟨0⟩ : UInt256))) (UInt256.ofNat 128)) :: x0 :: (UInt256.ofNat 8673) :: ((UInt256.ofNat 1) + (keccakWord x6 (UInt256.ofNat 64) (x1.toByteArray.write 0 (x8.toByteArray.write 0 mem x6.toNat 32) x2.toNat 32))) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Final memory for bytecode block summary `morpho_block_8645`. -/
def morpho_block_8645_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x6 : UInt256} {x8 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 (x8.toByteArray.write 0 mem x6.toNat 32) x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8645. -/
theorem morpho_block_8645 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12664) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8645) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12664) (morpho_block_8645_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (morpho_block_8645_memory (mem := mem) (x1 := x1) (x2 := x2) (x6 := x6) (x8 := x8)) (M (M (M aw x6 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x6 (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8645⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8646⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8647⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8648⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8649⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8650⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8651⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8653⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8654⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8655⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8657⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8658⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8659⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8660⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8661⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.shr (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8663⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8664⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8673) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8665⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8673), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8668⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 12664) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8669⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12664), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8672⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12664)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8645_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12664) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8645) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12664) (morpho_block_8645_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (morpho_block_8645_memory (mem := mem) (x1 := x1) (x2 := x2) (x6 := x6) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8645 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8673`. -/
def morpho_block_8673_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {x14 : UInt256} {R : List UInt256} : List UInt256 :=
  (x12 :: (UInt256.ofNat 8747) :: x4 :: x14 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8673. -/
theorem morpho_block_8673 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15480) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8673) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15480) (morpho_block_8673_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x1 (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (UInt256.shiftLeft x0 (UInt256.ofNat 128))) (UInt256.land (UInt256.ofNat 340282366920938463463374607431768211455) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8673⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8674⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8675⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 340282366920938463463374607431768211455) (width := 16) (op := .PUSH16) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8676⟩ : UInt256), UInt8.ofNat 111, .Push .PUSH16, some ((UInt256.ofNat 340282366920938463463374607431768211455), 16), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8693⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8694⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8696⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8697⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8698⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8699⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8700⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8733⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8734⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8735⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sstore r14 hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8736⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup13 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8737⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8738⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8747) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8739⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8747), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup14 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8742⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 15480) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8743⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15480), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8746⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15480)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8673_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 15480) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8673) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 15480) (morpho_block_8673_stack (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x1 (UInt256.lor (UInt256.land (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (UInt256.shiftLeft x0 (UInt256.ofNat 128))) (UInt256.land (UInt256.ofNat 340282366920938463463374607431768211455) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8673 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8747`. -/
def morpho_block_8747_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 1) + (keccakWord x6 (UInt256.ofNat 64) (x1.toByteArray.write 0 (x8.toByteArray.write 0 mem x6.toNat 32) x2.toNat 32))) (⟨0⟩ : UInt256))) x7) :: x0 :: (UInt256.ofNat 8777) :: x7 :: x3 :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 1) + (keccakWord x6 (UInt256.ofNat 64) (x1.toByteArray.write 0 (x8.toByteArray.write 0 mem x6.toNat 32) x2.toNat 32))) (⟨0⟩ : UInt256))) :: ((UInt256.ofNat 1) + (keccakWord x6 (UInt256.ofNat 64) (x1.toByteArray.write 0 (x8.toByteArray.write 0 mem x6.toNat 32) x2.toNat 32))) :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Final memory for bytecode block summary `morpho_block_8747`. -/
def morpho_block_8747_memory {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x6 : UInt256} {x8 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 (x8.toByteArray.write 0 mem x6.toNat 32) x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8747. -/
theorem morpho_block_8747 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12664) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8747) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12664) (morpho_block_8747_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (morpho_block_8747_memory (mem := mem) (x1 := x1) (x2 := x2) (x6 := x6) (x8 := x8)) (M (M (M aw x6 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x6 (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8747⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8748⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8749⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8750⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8751⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8752⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8753⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8755⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8756⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8757⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8759⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8760⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup7 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8761⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8762⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8763⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8764⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8765⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8766⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8767⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8768⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8777) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8769⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8777), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8772⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 12664) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8773⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12664), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8776⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12664)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8747_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12664) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8747) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12664) (morpho_block_8747_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (morpho_block_8747_memory (mem := mem) (x1 := x1) (x2 := x2) (x6 := x6) (x8 := x8)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8747 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8777`. -/
def morpho_block_8777_stack {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  (x12 :: x9 :: x5 :: (UInt256.ofNat 8794) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8777. -/
theorem morpho_block_8777 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 13948) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8777) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 13948) (morpho_block_8777_stack (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x4 (UInt256.lor (UInt256.land x3 x2) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8777⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8778⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8779⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8780⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8781⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8782⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sstore r6 hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8783⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8794) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8784⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8794), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8787⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8788⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup10 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8789⟩ : UInt256), UInt8.ofNat 137, .DUP10, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 13948) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8790⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13948), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8793⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13948)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8777_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 13948) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8777) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 13948) (morpho_block_8777_stack (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x4 (UInt256.lor (UInt256.land x3 x2) (UInt256.land x0 x1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8777 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8794`. -/
def morpho_block_8794_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 8802) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8794. -/
theorem morpho_block_8794 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12937) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8794) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12937) (morpho_block_8794_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8794⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8802) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8795⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8802), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 12937) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8798⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12937), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8801⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12937)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8794_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12937) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8794) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12937) (morpho_block_8794_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8794 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8802`. -/
def morpho_block_8802_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.ofNat 8811) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8802. -/
theorem morpho_block_8802 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8802) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8802_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8802⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8811) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8803⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8811), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8806⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 12097) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8807⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12097), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8810⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12097)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8802_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8802) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8802_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8802 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8811`. -/
def morpho_block_8811_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 8841) :: (UInt256.isZero (UInt256.lt (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x1 (UInt256.ofNat 64) (x0.toByteArray.write 0 (x3.toByteArray.write 0 mem x1.toNat 32) x10.toNat 32)) (⟨0⟩ : UInt256))) x2) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x1 (UInt256.ofNat 64) (x0.toByteArray.write 0 (x3.toByteArray.write 0 mem x1.toNat 32) x10.toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) x2))) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `morpho_block_8811`. -/
def morpho_block_8811_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x10 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 (x3.toByteArray.write 0 mem x1.toNat 32) x10.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8811. -/
theorem morpho_block_8811 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12880) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8811) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12880) (morpho_block_8811_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (morpho_block_8811_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x10 := x10)) (M (M (M aw x1 (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) x1 (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8811⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8812⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8813⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8814⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8815⟩ : UInt256), UInt8.ofNat 138, .DUP11, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8816⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8817⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8819⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8820⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8821⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8822⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8823⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8825⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8826⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8827⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8828⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8829⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8830⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8831⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.lt (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8832⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.iszero (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8833⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 8841) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8834⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8841), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 12880) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8837⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12880), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8840⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12880)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8811_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12880) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8811) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12880) (morpho_block_8811_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (morpho_block_8811_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x10 := x10)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := morpho_block_8811 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morpho_block_8841`. -/
def morpho_block_8841_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.ofNat 8850) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8841. -/
theorem morpho_block_8841 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8841) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8841_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8841⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8850) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8842⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8850), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8845⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 12097) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8846⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12097), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, immWords, (⟨8849⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12097)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morpho_block_8841_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 8841) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.immutableLayout.runtime Benchmarks.Morpho.MorphoBlue.morphoBytecode immWords) ee g s0 (UInt256.ofNat 12097) (morpho_block_8841_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morpho_block_8841 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end morphoBlocks
