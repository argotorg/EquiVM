import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode
import Benchmarks.Morpho.MetaMorphoV1_1.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace metaMorphoV1_1Blocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.sites = [(8892, 32, "_asset"), (9554, 32, "_asset"), (14624, 32, "_asset"), (15675, 32, "_asset"), (9752, 32, "_underlyingDecimals"), (12952, 32, "_cachedDomainSeparator"), (13141, 32, "_cachedChainId"), (12898, 32, "_cachedThis"), (13031, 32, "_hashedName"), (13069, 32, "_hashedVersion"), (4899, 32, "_name"), (4940, 32, "_version"), (6184, 32, "MORPHO"), (6494, 32, "MORPHO"), (8484, 32, "MORPHO"), (9021, 32, "MORPHO"), (9486, 32, "MORPHO"), (12214, 32, "MORPHO"), (13651, 32, "MORPHO"), (13860, 32, "MORPHO"), (14958, 32, "MORPHO"), (15902, 32, "MORPHO"), (16145, 32, "MORPHO"), (17851, 32, "MORPHO"), (18804, 32, "MORPHO"), (19479, 32, "MORPHO"), (3680, 32, "DECIMALS_OFFSET"), (9716, 32, "DECIMALS_OFFSET"), (14387, 32, "DECIMALS_OFFSET"), (14457, 32, "DECIMALS_OFFSET"), (15259, 32, "DECIMALS_OFFSET"), (15326, 32, "DECIMALS_OFFSET")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.inBounds Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords).size = Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18126_taken`. -/
def metaMorphoV1_1_block_18126_taken_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18126. -/
theorem metaMorphoV1_1_block_18126_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12537) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18126) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12537) (metaMorphoV1_1_block_18126_taken_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18126⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18127⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18128⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18129⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18130⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12537) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18131⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12537), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18134⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12537)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18126_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12537) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18126) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12537) (metaMorphoV1_1_block_18126_taken_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18126_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18126_fallthrough`. -/
def metaMorphoV1_1_block_18126_fallthrough_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18126. -/
theorem metaMorphoV1_1_block_18126_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18126) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18135) (metaMorphoV1_1_block_18126_fallthrough_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18126⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18127⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18128⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18129⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18130⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12537) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18131⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12537), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18134⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18135)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18126_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x4) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18126) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18135) (metaMorphoV1_1_block_18126_fallthrough_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18126_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18135`. -/
def metaMorphoV1_1_block_18135_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 18135. -/
theorem metaMorphoV1_1_block_18135 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18135) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18138) (metaMorphoV1_1_block_18135_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 2) (C + ((6))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18135⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18137⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18138)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18135_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18135) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18138) (metaMorphoV1_1_block_18135_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18135 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18138`. -/
def metaMorphoV1_1_block_18138_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 18138. -/
theorem metaMorphoV1_1_block_18138 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 17895) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18138) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 17895) (metaMorphoV1_1_block_18138_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18138⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18139⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 17895) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18140⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 17895), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18143⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17895)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18138_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 17895) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18138) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 17895) (metaMorphoV1_1_block_18138_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18138 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18144`. -/
def metaMorphoV1_1_block_18144_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) :: x0 :: x1 :: (UInt256.ofNat ee.codeOwner.val) :: (UInt256.ofNat 18178) :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 64) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_18144`. -/
def metaMorphoV1_1_block_18144_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 2845486473) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 18144. -/
theorem metaMorphoV1_1_block_18144 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12133) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18144) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12133) (metaMorphoV1_1_block_18144_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1_block_18144_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18144⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18145⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18178) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18147⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18178), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18150⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18151⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMload r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18152⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18153⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18154⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18155⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18156⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push4 (UInt256.ofNat 2845486473) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18157⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2845486473), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 224) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18162⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18164⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18165⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18166⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18167⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.address (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18168⟩ : UInt256), UInt8.ofNat 48, .ADDRESS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18169⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18170⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18172⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18173⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 12133) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18174⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12133), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18177⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12133)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18144_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12133) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18144) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12133) (metaMorphoV1_1_block_18144_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1_block_18144_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18144 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18178`. -/
def metaMorphoV1_1_block_18178_stack {g : Sat256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((12)) + 2)).toUInt256) :: x7 :: (⟨0⟩ : UInt256) :: x2 :: (UInt256.sub x0 x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18178. -/
theorem metaMorphoV1_1_block_18178 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18178) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18184) (metaMorphoV1_1_block_18178_stack (g := g) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 6) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18178⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18179⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18180⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18181⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18182⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genGas (RD.normalizeCounters (k' := k + 5) (C' := C + ((12))) r5 (by omega) (by omega)) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18183⟩ : UInt256), UInt8.ofNat 90, .GAS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18184)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18178_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18178) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18184) (metaMorphoV1_1_block_18178_stack (g := g) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18178 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 18184: call (0xf1). No RD transition is asserted. Summaries resume at pc 18185 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18185_taken`. -/
def metaMorphoV1_1_block_18185_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18185. -/
theorem metaMorphoV1_1_block_18185_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18220) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18185) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18220) (metaMorphoV1_1_block_18185_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18185⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18186⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18220) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18187⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18220), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18190⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18220)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18185_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18220) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18185) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18220) (metaMorphoV1_1_block_18185_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18185_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18185_fallthrough`. -/
def metaMorphoV1_1_block_18185_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18185. -/
theorem metaMorphoV1_1_block_18185_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18185) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (metaMorphoV1_1_block_18185_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18185⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18186⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18220) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18187⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18220), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18190⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18191)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18185_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18185) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (metaMorphoV1_1_block_18185_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18185_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18191_taken`. -/
def metaMorphoV1_1_block_18191_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 18191. -/
theorem metaMorphoV1_1_block_18191_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18203) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18203) (metaMorphoV1_1_block_18191_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18191⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18192⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18203) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18193⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18203), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18196⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18203)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18191_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18203) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18203) (metaMorphoV1_1_block_18191_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18191_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18191_fallthrough`. -/
def metaMorphoV1_1_block_18191_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 18191. -/
theorem metaMorphoV1_1_block_18191_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18197) (metaMorphoV1_1_block_18191_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18191⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18192⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18203) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18193⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18203), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18196⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18197)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18191_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18197) (metaMorphoV1_1_block_18191_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18191_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18197`. -/
def metaMorphoV1_1_block_18197_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18197. -/
theorem metaMorphoV1_1_block_18197 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18126) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18197) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18126) (metaMorphoV1_1_block_18197_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18197⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18198⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18126) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18199⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18126), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18202⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18126)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18197_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18126) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18197) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18126) (metaMorphoV1_1_block_18197_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18197 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18203`. -/
def metaMorphoV1_1_block_18203_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x0 :: (UInt256.ofNat 18213) :: x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18203. -/
theorem metaMorphoV1_1_block_18203 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12192) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18203) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12192) (metaMorphoV1_1_block_18203_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18203⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18213) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18204⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18213), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18207⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18208⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18209⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12192), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18212⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12192)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18203_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12192) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18203) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12192) (metaMorphoV1_1_block_18203_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18203 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18213`. -/
def metaMorphoV1_1_block_18213_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18213. -/
theorem metaMorphoV1_1_block_18213 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18197) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18213) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18197) (metaMorphoV1_1_block_18213_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18213⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18214⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18215⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 18197) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18216⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18197), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18219⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18197)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18213_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18197) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18213) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18197) (metaMorphoV1_1_block_18213_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18213 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18220_taken`. -/
def metaMorphoV1_1_block_18220_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 64) :: x0 :: (UInt256.ofNat 18243) :: R)

/-- Automatically generated RD summary for bytecode block at pc 18220. -/
theorem metaMorphoV1_1_block_18220_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 6359) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18220) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 6359) (metaMorphoV1_1_block_18220_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18220⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18243) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18221⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18243), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18224⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18225⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18227⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18228⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18229⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6359) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18230⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6359), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18233⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6359)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18220_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 6359) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18220) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 6359) (metaMorphoV1_1_block_18220_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18220_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18220_fallthrough`. -/
def metaMorphoV1_1_block_18220_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 64) :: x0 :: (UInt256.ofNat 18243) :: R)

/-- Automatically generated RD summary for bytecode block at pc 18220. -/
theorem metaMorphoV1_1_block_18220_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18220) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18234) (metaMorphoV1_1_block_18220_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18220⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18243) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18221⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18243), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18224⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18225⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18227⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18228⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18229⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6359) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18230⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6359), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18233⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18234)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18220_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 64) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18220) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18234) (metaMorphoV1_1_block_18220_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18220_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18234`. -/
def metaMorphoV1_1_block_18234_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.ofNat 6342) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18234. -/
theorem metaMorphoV1_1_block_18234 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11287) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18234) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11287) (metaMorphoV1_1_block_18234_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 6342) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18234⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 6342), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18237⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18238⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11287) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18239⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11287), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18242⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11287)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18234_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11287) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18234) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11287) (metaMorphoV1_1_block_18234_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18234 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18243`. -/
def metaMorphoV1_1_block_18243_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 18243. -/
theorem metaMorphoV1_1_block_18243 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18191) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18243) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (metaMorphoV1_1_block_18243_stack (R := R)) mem aw rdata σ (k + 4) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18243⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18244⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18191) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18245⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18191), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18248⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18191)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18243_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18191) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18243) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18191) (metaMorphoV1_1_block_18243_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18243 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18249_taken`. -/
def metaMorphoV1_1_block_18249_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 192) :: x0 :: (UInt256.ofNat 18278) :: (UInt256.ofNat 18077) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18249. -/
theorem metaMorphoV1_1_block_18249_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15192) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18249) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15192) (metaMorphoV1_1_block_18249_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 13) (C + ((42))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18249⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18077) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18250⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18077), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18253⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18254⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18255⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 18278) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18256⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18278), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18259⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18260⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18262⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18263⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.gt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18264⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 15192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18265⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15192), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18268⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15192)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18249_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15192) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18249) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15192) (metaMorphoV1_1_block_18249_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18249_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18249_fallthrough`. -/
def metaMorphoV1_1_block_18249_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 192) :: x0 :: (UInt256.ofNat 18278) :: (UInt256.ofNat 18077) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18249. -/
theorem metaMorphoV1_1_block_18249_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18249) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18269) (metaMorphoV1_1_block_18249_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 13) (C + ((42))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18249⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 18077) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18250⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18077), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18253⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18254⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18255⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 18278) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18256⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18278), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18259⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18260⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18262⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18263⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.gt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18264⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 15192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18265⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15192), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18268⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18269)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18249_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18249) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18269) (metaMorphoV1_1_block_18249_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18249_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_18269`. -/
def metaMorphoV1_1_block_18269_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.ofNat 15176) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 18269. -/
theorem metaMorphoV1_1_block_18269 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11287) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18269) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11287) (metaMorphoV1_1_block_18269_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 15176) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18269⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15176), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18272⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18273⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11287) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18274⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11287), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨18277⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11287)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_18269_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11287) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18269) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11287) (metaMorphoV1_1_block_18269_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_18269 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1Blocks
