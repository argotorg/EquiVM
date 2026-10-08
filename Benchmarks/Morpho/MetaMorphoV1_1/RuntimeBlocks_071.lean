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

theorem immutableDecode_15325 (immWords : String → UInt256) :
    decode (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) (⟨15325⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "DECIMALS_OFFSET", 32)) := by
  exact Layout.decodeSite (pc := (⟨15325⟩ : UInt256)) (words := immWords)
    15326 "DECIMALS_OFFSET" [(8892, immWords "_asset"), (9554, immWords "_asset"), (14624, immWords "_asset"), (15675, immWords "_asset"), (9752, immWords "_underlyingDecimals"), (12952, immWords "_cachedDomainSeparator"), (13141, immWords "_cachedChainId"), (12898, immWords "_cachedThis"), (13031, immWords "_hashedName"), (13069, immWords "_hashedVersion"), (4899, immWords "_name"), (4940, immWords "_version"), (6184, immWords "MORPHO"), (6494, immWords "MORPHO"), (8484, immWords "MORPHO"), (9021, immWords "MORPHO"), (9486, immWords "MORPHO"), (12214, immWords "MORPHO"), (13651, immWords "MORPHO"), (13860, immWords "MORPHO"), (14958, immWords "MORPHO"), (15902, immWords "MORPHO"), (16145, immWords "MORPHO"), (17851, immWords "MORPHO"), (18804, immWords "MORPHO"), (19479, immWords "MORPHO"), (3680, immWords "DECIMALS_OFFSET"), (9716, immWords "DECIMALS_OFFSET"), (14387, immWords "DECIMALS_OFFSET"), (14457, immWords "DECIMALS_OFFSET"), (15259, immWords "DECIMALS_OFFSET")] []
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

theorem immutableDecode_15674 (immWords : String → UInt256) :
    decode (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) (⟨15674⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "_asset", 32)) := by
  exact Layout.decodeSite (pc := (⟨15674⟩ : UInt256)) (words := immWords)
    15675 "_asset" [(8892, immWords "_asset"), (9554, immWords "_asset"), (14624, immWords "_asset")] [(9752, immWords "_underlyingDecimals"), (12952, immWords "_cachedDomainSeparator"), (13141, immWords "_cachedChainId"), (12898, immWords "_cachedThis"), (13031, immWords "_hashedName"), (13069, immWords "_hashedVersion"), (4899, immWords "_name"), (4940, immWords "_version"), (6184, immWords "MORPHO"), (6494, immWords "MORPHO"), (8484, immWords "MORPHO"), (9021, immWords "MORPHO"), (9486, immWords "MORPHO"), (12214, immWords "MORPHO"), (13651, immWords "MORPHO"), (13860, immWords "MORPHO"), (14958, immWords "MORPHO"), (15902, immWords "MORPHO"), (16145, immWords "MORPHO"), (17851, immWords "MORPHO"), (18804, immWords "MORPHO"), (19479, immWords "MORPHO"), (3680, immWords "DECIMALS_OFFSET"), (9716, immWords "DECIMALS_OFFSET"), (14387, immWords "DECIMALS_OFFSET"), (14457, immWords "DECIMALS_OFFSET"), (15259, immWords "DECIMALS_OFFSET"), (15326, immWords "DECIMALS_OFFSET")]
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

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15295`. -/
def metaMorphoV1_1_block_15295_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15295. -/
theorem metaMorphoV1_1_block_15295 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 17769) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15295) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 17769) (metaMorphoV1_1_block_15295_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15295⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15296⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 17769) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15297⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 17769), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15300⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17769)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15295_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 17769) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15295) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 17769) (metaMorphoV1_1_block_15295_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15295 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15301_taken`. -/
def metaMorphoV1_1_block_15301_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (x2 + (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15301. -/
theorem metaMorphoV1_1_block_15301_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x2 (x2 + (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 9405) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15301) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 9405) (metaMorphoV1_1_block_15301_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15301⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15302⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15304⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15305⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15306⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15307⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15308⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 9405) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15309⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9405), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15312⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9405)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15301_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x2 (x2 + (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 9405) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15301) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 9405) (metaMorphoV1_1_block_15301_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15301_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15301_fallthrough`. -/
def metaMorphoV1_1_block_15301_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: (x2 + (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15301. -/
theorem metaMorphoV1_1_block_15301_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x2 (x2 + (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15301) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15313) (metaMorphoV1_1_block_15301_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15301⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15302⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15304⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15305⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15306⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15307⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.gt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15308⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 9405) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15309⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 9405), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15312⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15313)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15301_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x2 (x2 + (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15301) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15313) (metaMorphoV1_1_block_15301_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15301_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15313`. -/
def metaMorphoV1_1_block_15313_stack {immWords : String → UInt256} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((immWords "DECIMALS_OFFSET") :: (UInt256.ofNat 12473) :: x1 :: (UInt256.ofNat 15295) :: x2 :: x0 :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 11715) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15313. -/
theorem metaMorphoV1_1_block_15313 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 14360) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15313) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 14360) (metaMorphoV1_1_block_15313_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 9) (C + ((31))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 11715) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15313⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11715), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15316⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 15295) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15317⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15295), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15320⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15321⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 12473) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15322⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12473), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (immWords "DECIMALS_OFFSET") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨15325⟩ : UInt256)
    exact immutableDecode_15325 immWords) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 14360) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15358⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14360), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15361⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14360)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15313_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 14360) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15313) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 14360) (metaMorphoV1_1_block_15313_stack (immWords := immWords) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15313 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15362`. -/
def metaMorphoV1_1_block_15362_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 15362. -/
theorem metaMorphoV1_1_block_15362 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15362) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 x1 (metaMorphoV1_1_block_15362_stack (R := R)) mem (M aw (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 12) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256)))))) (UInt256.ofNat 15) (⟨0⟩ : UInt256)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15362⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 12) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15363⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 12), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15365⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15366⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15367⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15369⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15371⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15373⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15374⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15375⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15376⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15377⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15379⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15381⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15383⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15384⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15385⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15386⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15387⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15388⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15389⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15390⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.or (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15391⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15392⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sstore r24 hperm (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15393⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.caller (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15394⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.pushConst (UInt256.ofNat 91850956357544086919000203399145793885577938156695971640712153106621572937443) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15395⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 91850956357544086919000203399145793885577938156695971640712153106621572937443), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15428⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15429⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := RD.genLog3 r29 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15430⟩ : UInt256), UInt8.ofNat 163, .LOG3, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r31 := r30.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15431⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 15) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15432⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 15), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r33⟩ := RD.sstore r32 hperm (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15434⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15435⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact ⟨_, _, r34⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15362_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15362) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 x1 (metaMorphoV1_1_block_15362_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 12) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 12) (⟨0⟩ : UInt256)))))) (UInt256.ofNat 15) (⟨0⟩ : UInt256)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_15362 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15436. -/
theorem metaMorphoV1_1_block_15436_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15478) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15436) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15478) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15436⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15437⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15438⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 15478) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15439⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15478), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15442⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15478)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15436_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15478) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15436) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15478) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15436_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15436. -/
theorem metaMorphoV1_1_block_15436_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15436) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15443) R mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15436⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15437⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15438⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 15478) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15439⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15478), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15442⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15443)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15436_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15436) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15443) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15436_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15443`. -/
def metaMorphoV1_1_block_15443_stack {rdata : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (UInt256.ofNat 15453) :: x0 :: (UInt256.ofNat rdata.size) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15443. -/
theorem metaMorphoV1_1_block_15443 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11575) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15443) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11575) (metaMorphoV1_1_block_15443_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15443⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15444⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 15453) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15445⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15453), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15448⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11575) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15449⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11575), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15452⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11575)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15443_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11575) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15443) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11575) (metaMorphoV1_1_block_15443_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15443 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15453`. -/
def metaMorphoV1_1_block_15453_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: x0 :: (UInt256.ofNat 15467) :: x2 :: x1 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15453. -/
theorem metaMorphoV1_1_block_15453 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11287) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15453) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11287) (metaMorphoV1_1_block_15453_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15453⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15454⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 15467) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15455⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15467), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15458⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15460⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15461⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15462⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 11287) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15463⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11287), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15466⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11287)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15453_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11287) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15453) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11287) (metaMorphoV1_1_block_15453_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15453 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15467`. -/
def metaMorphoV1_1_block_15467_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_15467`. -/
def metaMorphoV1_1_block_15467_memory {mem : ByteArray} {rdata : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  (rdata.write (⟨0⟩ : UInt256).toNat (x0.toByteArray.write 0 mem x2.toNat 32) (x2 + (UInt256.ofNat 32)).toNat (UInt256.ofNat rdata.size).toNat)

/-- Automatically generated RD summary for bytecode block at pc 15467. -/
theorem metaMorphoV1_1_block_15467 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15467) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 x1 (metaMorphoV1_1_block_15467_stack (x2 := x2) (R := R)) (metaMorphoV1_1_block_15467_memory (mem := mem) (rdata := rdata) (x0 := x0) (x2 := x2)) (M (M aw x2 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (UInt256.ofNat rdata.size)) rdata σ (k + 10) (C + ((28) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 32)) (UInt256.ofNat rdata.size)) + (3 + 3 * (((UInt256.ofNat rdata.size).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15467⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15468⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15469⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.returndatasize (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15470⟩ : UInt256), UInt8.ofNat 61, .RETURNDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15471⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15472⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15474⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.add (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15475⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genReturndatacopy r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15476⟩ : UInt256), UInt8.ofNat 62, .RETURNDATACOPY, none, immutableLayout_inBounds, immutableTemplate_size64)) hguard0 (by evm_ov)
  have r10 := r9.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15477⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15467_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hguard0 : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains x1 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15467) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 x1 (metaMorphoV1_1_block_15467_stack (x2 := x2) (R := R)) (metaMorphoV1_1_block_15467_memory (mem := mem) (rdata := rdata) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15467 hstack hguard0 hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15478`. -/
def metaMorphoV1_1_block_15478_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 96) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15478. -/
theorem metaMorphoV1_1_block_15478 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15478) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 x0 (metaMorphoV1_1_block_15478_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15478⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15479⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15481⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15482⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15478_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains x0 = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15478) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 x0 (metaMorphoV1_1_block_15478_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15478 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15483`. -/
def metaMorphoV1_1_block_15483_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 22) (⟨0⟩ : UInt256))) x3) (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 22) (⟨0⟩ : UInt256))) x3)) :: (UInt256.ofNat 15503) :: x4 :: x1 :: x0 :: x3 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15483. -/
theorem metaMorphoV1_1_block_15483 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 16788) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15483) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 16788) (metaMorphoV1_1_block_15483_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15483⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15484⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15485⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 15503) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15486⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15503), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 22) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15489⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 22), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15491⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15492⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15493⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15494⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15495⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15496⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.gt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15497⟩ : UInt256), UInt8.ofNat 17, .GT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.mul (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15498⟩ : UInt256), UInt8.ofNat 2, .MUL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 16788) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15499⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 16788), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15502⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16788)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15483_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 16788) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15483) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 16788) (metaMorphoV1_1_block_15483_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_15483 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15503`. -/
def metaMorphoV1_1_block_15503_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.ofNat 15512) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15503. -/
theorem metaMorphoV1_1_block_15503 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18619) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15503) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18619) (metaMorphoV1_1_block_15503_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15503⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 15512) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15504⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15512), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15507⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 18619) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15508⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18619), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15511⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18619)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15503_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 18619) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15503) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 18619) (metaMorphoV1_1_block_15503_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15503 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15512_taken`. -/
def metaMorphoV1_1_block_15512_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x4 :: x0 :: x1 :: (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x3 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15512. -/
theorem metaMorphoV1_1_block_15512_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15759) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15512) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15759) (metaMorphoV1_1_block_15512_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 21) (C + ((68))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15512⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15513⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15515⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15517⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15519⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15520⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15521⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15522⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15523⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15524⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15525⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15526⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15527⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15528⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15529⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15530⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15531⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15532⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15533⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 15759) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15534⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15759), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15537⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15759)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15512_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15759) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15512) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15759) (metaMorphoV1_1_block_15512_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15512_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15512_fallthrough`. -/
def metaMorphoV1_1_block_15512_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x4 :: x0 :: x1 :: (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x3 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4) :: R)

/-- Automatically generated RD summary for bytecode block at pc 15512. -/
theorem metaMorphoV1_1_block_15512_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15512) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15538) (metaMorphoV1_1_block_15512_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 21) (C + ((68))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15512⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15513⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15515⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15517⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15519⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15520⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15521⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15522⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15523⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15524⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15525⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15526⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15527⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15528⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15529⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15530⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.dup8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15531⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15532⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15533⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 15759) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15534⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15759), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15537⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15538)) r21 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15512_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15512) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15538) (metaMorphoV1_1_block_15512_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15512_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15538_taken`. -/
def metaMorphoV1_1_block_15538_taken_stack {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15538. -/
theorem metaMorphoV1_1_block_15538_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x7) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12856) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15538) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12856) (metaMorphoV1_1_block_15538_taken_stack (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 8) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15538⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15539⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15540⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15541⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15542⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15543⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 12856) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15544⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12856), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15547⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12856)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15538_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x7) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12856) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15538) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12856) (metaMorphoV1_1_block_15538_taken_stack (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15538_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15538_fallthrough`. -/
def metaMorphoV1_1_block_15538_fallthrough_stack {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 15538. -/
theorem metaMorphoV1_1_block_15538_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x7) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15538) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15548) (metaMorphoV1_1_block_15538_fallthrough_stack (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 8) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15538⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15539⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15540⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15541⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15542⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15543⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 12856) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15544⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12856), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15547⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15548)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15538_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero x7) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15538) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15548) (metaMorphoV1_1_block_15538_fallthrough_stack (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_15538_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15548_taken`. -/
def metaMorphoV1_1_block_15548_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_15548_taken`. -/
def metaMorphoV1_1_block_15548_taken_memory {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 15548. -/
theorem metaMorphoV1_1_block_15548_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15734) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15548) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15734) (metaMorphoV1_1_block_15548_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (metaMorphoV1_1_block_15548_taken_memory (mem := mem) (x4 := x4)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15548⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15549⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15550⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15551⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15552⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15554⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15555⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15557⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15558⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15559⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15560⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15561⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.lt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15562⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 15734) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15563⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15734), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15566⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15734)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15548_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15734) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15548) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15734) (metaMorphoV1_1_block_15548_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (metaMorphoV1_1_block_15548_taken_memory (mem := mem) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_15548_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15548_fallthrough`. -/
def metaMorphoV1_1_block_15548_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_15548_fallthrough`. -/
def metaMorphoV1_1_block_15548_fallthrough_memory {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 15548. -/
theorem metaMorphoV1_1_block_15548_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15548) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15567) (metaMorphoV1_1_block_15548_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (metaMorphoV1_1_block_15548_fallthrough_memory (mem := mem) (x4 := x4)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15548⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15549⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15550⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15551⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15552⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15554⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15555⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15557⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15558⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15559⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15560⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15561⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.lt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15562⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 15734) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15563⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15734), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15566⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15567)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15548_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x4.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15548) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15567) (metaMorphoV1_1_block_15548_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (metaMorphoV1_1_block_15548_fallthrough_memory (mem := mem) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_15548_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_15567`. -/
def metaMorphoV1_1_block_15567_stack {immWords : String → UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((immWords "_asset") :: x2 :: x4 :: (UInt256.ofNat 15711) :: x1 :: x2 :: (UInt256.ofNat 64) :: (UInt256.ofNat 113923603527463639014809444807069482138736635533632932454551718384408456251611) :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_15567`. -/
def metaMorphoV1_1_block_15567_memory {mem : ByteArray} {x1 : UInt256} {x5 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 15567. -/
theorem metaMorphoV1_1_block_15567 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15776) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15567) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15776) (metaMorphoV1_1_block_15567_stack (immWords := immWords) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (metaMorphoV1_1_block_15567_memory (mem := mem) (x1 := x1) (x5 := x5)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 32)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.sub x0 x1)) (UInt256.ofNat 2) (UInt256.sub ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) x1)) k' C' := by
  let r0 := h
  have r1 := r0.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15567⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15568⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15569⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15571⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 113923603527463639014809444807069482138736635533632932454551718384408456251611) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15572⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 113923603527463639014809444807069482138736635533632932454551718384408456251611), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15605⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15606⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15607⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15608⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15609⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15610⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15612⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15613⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15614⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15615⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15616⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sstore r16 hperm (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15617⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15618⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15619⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15621⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15622⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15623⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sstore r22 hperm (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15625⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15626⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15627⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.pushConst (UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15628⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15661⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.dup7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15663⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := RD.genMload r28 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15664⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15665⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15666⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := RD.genMstore r31 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15667⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := RD.genLog3 r32 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15668⟩ : UInt256), UInt8.ofNat 163, .LOG3, none, immutableLayout_inBounds, immutableTemplate_size64)) hperm (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 15711) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15669⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15711), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.dup7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15672⟩ : UInt256), UInt8.ofNat 134, .DUP7, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15673⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := r36.pushConst (immWords "_asset") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨15674⟩ : UInt256)
    exact immutableDecode_15674 immWords) (by evm_ov)
  have r38 := r37.push2 (UInt256.ofNat 15776) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15707⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 15776), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨15710⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15776)) r39 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_15567_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 15776) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15567) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 15776) (metaMorphoV1_1_block_15567_stack (immWords := immWords) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (metaMorphoV1_1_block_15567_memory (mem := mem) (x1 := x1) (x5 := x5)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.sub x0 x1)) (UInt256.ofNat 2) (UInt256.sub ((sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) x1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_15567 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1Blocks
