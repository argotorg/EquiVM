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
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.sites = [(8940, 32, "_asset"), (9602, 32, "_asset"), (14666, 32, "_asset"), (15717, 32, "_asset"), (9800, 32, "_underlyingDecimals"), (12994, 32, "_cachedDomainSeparator"), (13183, 32, "_cachedChainId"), (12940, 32, "_cachedThis"), (13073, 32, "_hashedName"), (13111, 32, "_hashedVersion"), (4972, 32, "_name"), (5013, 32, "_version"), (6257, 32, "MORPHO"), (6567, 32, "MORPHO"), (8532, 32, "MORPHO"), (9069, 32, "MORPHO"), (9534, 32, "MORPHO"), (12256, 32, "MORPHO"), (13693, 32, "MORPHO"), (13902, 32, "MORPHO"), (15000, 32, "MORPHO"), (15944, 32, "MORPHO"), (16187, 32, "MORPHO"), (17893, 32, "MORPHO"), (18846, 32, "MORPHO"), (19521, 32, "MORPHO"), (3730, 32, "DECIMALS_OFFSET"), (9764, 32, "DECIMALS_OFFSET"), (14429, 32, "DECIMALS_OFFSET"), (14499, 32, "DECIMALS_OFFSET"), (15301, 32, "DECIMALS_OFFSET"), (15368, 32, "DECIMALS_OFFSET")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.inBounds Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords).size = Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

theorem immutableDecode_8531 (immWords : String → UInt256) :
    decode (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) (⟨8531⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "MORPHO", 32)) := by
  exact Layout.decodeSite (pc := (⟨8531⟩ : UInt256)) (words := immWords)
    8532 "MORPHO" [(8940, immWords "_asset"), (9602, immWords "_asset"), (14666, immWords "_asset"), (15717, immWords "_asset"), (9800, immWords "_underlyingDecimals"), (12994, immWords "_cachedDomainSeparator"), (13183, immWords "_cachedChainId"), (12940, immWords "_cachedThis"), (13073, immWords "_hashedName"), (13111, immWords "_hashedVersion"), (4972, immWords "_name"), (5013, immWords "_version"), (6257, immWords "MORPHO"), (6567, immWords "MORPHO")] [(9069, immWords "MORPHO"), (9534, immWords "MORPHO"), (12256, immWords "MORPHO"), (13693, immWords "MORPHO"), (13902, immWords "MORPHO"), (15000, immWords "MORPHO"), (15944, immWords "MORPHO"), (16187, immWords "MORPHO"), (17893, immWords "MORPHO"), (18846, immWords "MORPHO"), (19521, immWords "MORPHO"), (3730, immWords "DECIMALS_OFFSET"), (9764, immWords "DECIMALS_OFFSET"), (14429, immWords "DECIMALS_OFFSET"), (14499, immWords "DECIMALS_OFFSET"), (15301, immWords "DECIMALS_OFFSET"), (15368, immWords "DECIMALS_OFFSET")]
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

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8460`. -/
def metaMorphoV1_1_block_8460_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 8469) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8460. -/
theorem metaMorphoV1_1_block_8460 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11491) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8460) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11491) (metaMorphoV1_1_block_8460_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8460⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8469) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8461⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8469), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8464⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11491) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8465⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11491), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8468⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11491)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8460_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11491) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8460) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11491) (metaMorphoV1_1_block_8460_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_8460 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8469_taken`. -/
def metaMorphoV1_1_block_8469_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8469_taken`. -/
def metaMorphoV1_1_block_8469_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8469. -/
theorem metaMorphoV1_1_block_8469_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8672) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8672) (metaMorphoV1_1_block_8469_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1_block_8469_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8469⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8470⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8471⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8472⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8474⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8475⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8476⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8477⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8478⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8479⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8480⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8481⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMstore r12 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8482⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 13) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8483⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8485⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genMstore r15 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8487⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8488⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8490⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8491⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8492⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8493⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8495⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 184) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8497⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8499⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8500⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8501⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 8672) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8502⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8672), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8505⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8672)) r28 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8469_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8672) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8672) (metaMorphoV1_1_block_8469_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1_block_8469_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8469_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8469_fallthrough`. -/
def metaMorphoV1_1_block_8469_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))) :: R)

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8469_fallthrough`. -/
def metaMorphoV1_1_block_8469_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8469. -/
theorem metaMorphoV1_1_block_8469_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8506) (metaMorphoV1_1_block_8469_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1_block_8469_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8469⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8470⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8471⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8472⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8474⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8475⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8476⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8477⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8478⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8479⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8480⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8481⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMstore r12 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8482⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 13) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8483⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8485⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genMstore r15 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8487⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8488⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8490⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8491⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8492⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8493⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8495⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 184) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8497⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8499⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.sub (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8500⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.and (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8501⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 8672) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8502⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8672), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8505⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8506)) r28 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8469_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8506) (metaMorphoV1_1_block_8469_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (metaMorphoV1_1_block_8469_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8469_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8506_taken`. -/
def metaMorphoV1_1_block_8506_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 16).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8506. -/
theorem metaMorphoV1_1_block_8506_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 5453) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8506) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 5453) (x0 :: R) (metaMorphoV1_1_block_8506_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8506⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8507⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8508⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 16) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8509⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 16), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8511⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8513⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8514⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8516⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8517⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8518⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8519⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8521⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5453) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8522⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5453), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8525⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5453)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8506_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 5453) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8506) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 5453) (x0 :: R) (metaMorphoV1_1_block_8506_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8506_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8506_fallthrough`. -/
def metaMorphoV1_1_block_8506_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 16).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8506. -/
theorem metaMorphoV1_1_block_8506_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8506) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8526) (x0 :: R) (metaMorphoV1_1_block_8506_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8506⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8507⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8508⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 16) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8509⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 16), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8511⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8513⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8514⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8516⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8517⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8518⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8519⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8521⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5453) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8522⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 5453), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8525⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8526)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8506_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8506) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8526) (x0 :: R) (metaMorphoV1_1_block_8506_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8506_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8526`. -/
def metaMorphoV1_1_block_8526_stack {immWords : String → UInt256} {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((immWords "MORPHO") :: x0 :: (UInt256.ofNat ee.codeOwner.val) :: (UInt256.ofNat 8568) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8526. -/
theorem metaMorphoV1_1_block_8526 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 14078) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8526) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 14078) (metaMorphoV1_1_block_8526_stack (immWords := immWords) (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 8568) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8526⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8568), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.address (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8529⟩ : UInt256), UInt8.ofNat 48, .ADDRESS, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8530⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (immWords "MORPHO") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨8531⟩ : UInt256)
    exact immutableDecode_8531 immWords) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14078) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8564⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14078), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8567⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14078)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8526_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 14078) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8526) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 14078) (metaMorphoV1_1_block_8526_stack (immWords := immWords) (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_8526 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8568_taken`. -/
def metaMorphoV1_1_block_8568_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8568. -/
theorem metaMorphoV1_1_block_8568_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8592) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8568) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8592) (metaMorphoV1_1_block_8568_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8568⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8592) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8569⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8592), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8572⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8592)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8568_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8592) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8568) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8592) (metaMorphoV1_1_block_8568_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_8568_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8568_fallthrough`. -/
def metaMorphoV1_1_block_8568_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8568. -/
theorem metaMorphoV1_1_block_8568_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8568) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8573) (metaMorphoV1_1_block_8568_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8568⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8592) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8569⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8592), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8572⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8573)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8568_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8568) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8573) (metaMorphoV1_1_block_8568_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_8568_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8573`. -/
def metaMorphoV1_1_block_8573_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8573`. -/
def metaMorphoV1_1_block_8573_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8573. -/
theorem metaMorphoV1_1_block_8573 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8452) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8573) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8452) (metaMorphoV1_1_block_8573_stack (R := R)) (metaMorphoV1_1_block_8573_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8573⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8574⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8575⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8576⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8577⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 13) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8578⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8580⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8582⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8583⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8585⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8586⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sstore r11 hperm (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8587⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 8452) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8588⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8452), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8591⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8452)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8573_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8452) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8573) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8452) (metaMorphoV1_1_block_8573_stack (R := R)) (metaMorphoV1_1_block_8573_memory (mem := mem) (x0 := x0)) aw' rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8573 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8592_taken`. -/
def metaMorphoV1_1_block_8592_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8592. -/
theorem metaMorphoV1_1_block_8592_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8654) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8592) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8654) (x0 :: R) (metaMorphoV1_1_block_8592_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8592⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8593⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8594⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8595⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 13) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8596⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8598⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8600⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8601⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8603⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8604⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8605⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8606⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8608⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8609⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 8654) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8610⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8654), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8613⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8654)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8592_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8654) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8592) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8654) (x0 :: R) (metaMorphoV1_1_block_8592_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8592_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8592_fallthrough`. -/
def metaMorphoV1_1_block_8592_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8592. -/
theorem metaMorphoV1_1_block_8592_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8592) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8614) (x0 :: R) (metaMorphoV1_1_block_8592_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8592⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8593⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8594⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8595⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 13) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8596⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8598⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8600⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8601⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8603⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8604⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8605⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8606⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8608⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8609⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 8654) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8610⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8654), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8613⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8614)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8592_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8592) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8614) (x0 :: R) (metaMorphoV1_1_block_8592_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8592_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8614_taken`. -/
def metaMorphoV1_1_block_8614_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8614. -/
theorem metaMorphoV1_1_block_8614_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8573) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8614) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8573) (x0 :: R) (metaMorphoV1_1_block_8614_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8614⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8615⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8616⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 13) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8617⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8619⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8621⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8622⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8624⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8625⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8626⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8627⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8629⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.timestamp (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8630⟩ : UInt256), UInt8.ofNat 66, .TIMESTAMP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.lt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8631⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8632⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 8573) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8633⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8573), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8636⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8573)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8614_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8573) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8614) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8573) (x0 :: R) (metaMorphoV1_1_block_8614_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8614_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `metaMorphoV1_1_block_8614_fallthrough`. -/
def metaMorphoV1_1_block_8614_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8614. -/
theorem metaMorphoV1_1_block_8614_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8614) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8637) (x0 :: R) (metaMorphoV1_1_block_8614_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8614⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8615⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMstore r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8616⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 13) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8617⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8619⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8621⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8622⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8624⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genKeccak256 r8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8625⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8626⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 192) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8627⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8629⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.timestamp (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8630⟩ : UInt256), UInt8.ofNat 66, .TIMESTAMP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.lt (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8631⟩ : UInt256), UInt8.ofNat 16, .LT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.iszero (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8632⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 8573) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8633⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8573), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jumpiNT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8636⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8637)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8614_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.header.timestamp) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 192)))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8614) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8637) (x0 :: R) (metaMorphoV1_1_block_8614_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8614_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8637. -/
theorem metaMorphoV1_1_block_8637 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8637) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 752161177) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8637⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 752161177), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 226) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8642⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 226), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8644⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8645⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8646⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8647⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8649⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8650⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8652⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r9 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8653⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 8654. -/
theorem metaMorphoV1_1_block_8654 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8654) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8654⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2945114759) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8655⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2945114759), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8660⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 224), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8662⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8663⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8664⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8665⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8667⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8668⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8670⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r10 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8671⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 8672. -/
theorem metaMorphoV1_1_block_8672 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8672) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8672⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1075676121) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8673⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1075676121), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 225) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8678⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 225), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8680⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8681⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8682⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8683⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8685⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 36) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8686⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 36), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push0 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8688⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r10 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8689⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8690`. -/
def metaMorphoV1_1_block_8690_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: x0 :: (UInt256.ofNat 8701) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8690. -/
theorem metaMorphoV1_1_block_8690 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11986) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8690) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11986) (metaMorphoV1_1_block_8690_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8690⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 8701) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8691⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8701), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8694⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup4 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8695⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup6 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8696⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11986) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8697⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11986), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8700⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11986)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8690_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11986) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8690) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11986) (metaMorphoV1_1_block_8690_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_8690 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8701`. -/
def metaMorphoV1_1_block_8701_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: (UInt256.ofNat 8711) :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8701. -/
theorem metaMorphoV1_1_block_8701 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11491) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8701) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11491) (metaMorphoV1_1_block_8701_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8701⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8702⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8711) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8703⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8711), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8706⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11491) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8707⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 11491), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8710⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11491)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8701_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 11491) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8701) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 11491) (metaMorphoV1_1_block_8701_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_8701 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8711`. -/
def metaMorphoV1_1_block_8711_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x6 :: x2 :: (UInt256.ofNat 8729) :: x2 :: (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))) :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8711. -/
theorem metaMorphoV1_1_block_8711 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12057) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8711) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12057) (metaMorphoV1_1_block_8711_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8711⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8712⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8713⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8714⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8715⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8717⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shr (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8718⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8719⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 8729) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8720⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8729), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8723⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup8 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8724⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 12057) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8725⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12057), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.jump (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8728⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12057)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8711_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 12057) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8711) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 12057) (metaMorphoV1_1_block_8711_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := metaMorphoV1_1_block_8711 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `metaMorphoV1_1_block_8729_taken`. -/
def metaMorphoV1_1_block_8729_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8729. -/
theorem metaMorphoV1_1_block_8729_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad x0 mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8767) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8729) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8767) (metaMorphoV1_1_block_8729_taken_stack (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((17) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8729⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMload r1 (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8730⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8767) (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8731⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8767), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jumpiT (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout, Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, immWords, (⟨8734⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8767)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem metaMorphoV1_1_block_8729_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad x0 mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) 0).contains (UInt256.ofNat 8767) = true)
    (h : RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8729) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout.runtime Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode immWords) ee g s0 (UInt256.ofNat 8767) (metaMorphoV1_1_block_8729_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (metaMorphoV1_1_block_8729_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end metaMorphoV1_1Blocks
