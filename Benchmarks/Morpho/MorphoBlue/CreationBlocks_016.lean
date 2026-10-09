import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Morpho.MorphoBlue.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace morphoCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode

/-- Final memory for bytecode block summary `morphoCreation_block_5336`. -/
def morphoCreation_block_5336_memory {mem : ByteArray} {x1 : UInt256} {x9 : UInt256} : ByteArray :=
  ((UInt256.ofNat 49474274355341680246294123618020960933857875614369968334246212219823082962944).toByteArray.write 0 ((UInt256.ofNat 22).toByteArray.write 0 mem x1.toNat 32) (x1 + x9).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5336. -/
theorem morphoCreation_block_5336 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5336) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12097) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) (morphoCreation_block_5336_memory (mem := mem) (x1 := x1) (x9 := x9)) (M (M aw x1 (⟨32⟩ : UInt256)) (x1 + x9) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (x1 + x9) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 22) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 49474274355341680246294123618020960933857875614369968334246212219823082962944) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 12097) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12097) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12097)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5336_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 12097) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5336) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12097) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) (morphoCreation_block_5336_memory (mem := mem) (x1 := x1) (x9 := x9)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5336 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5382`. -/
def morphoCreation_block_5382_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 64) :: x3 :: ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) :: (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) :: x1 :: (UInt256.ofNat 4) :: (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `morphoCreation_block_5382`. -/
def morphoCreation_block_5382_memory {mem : ByteArray} {x4 : UInt256} {x6 : UInt256} {x7 : UInt256} : ByteArray :=
  ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5382. -/
theorem morphoCreation_block_5382 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5382) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5519) (morphoCreation_block_5382_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (morphoCreation_block_5382_memory (mem := mem) (x4 := x4) (x6 := x6) (x7 := x7)) (M (M (M (M (M (M (M aw x7 (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) x7 (UInt256.ofNat 64)) x6 (⟨32⟩ : UInt256)) x7 (UInt256.ofNat 64)) x5 (⟨32⟩ : UInt256)) (x5 + x6) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))) (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960)) (UInt256.land (memLoad x5 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) x3))) ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) + (UInt256.ofNat 1)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))) (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960)) (UInt256.land (memLoad x5 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) x3))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960)) (UInt256.land (memLoad (x5 + x6) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) x3))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.timestamp (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sstore r21 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 8) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := RD.genMstore r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.dup9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := RD.genKeccak256 r28 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.dup8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := RD.genMload r32 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.pushConst (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r39⟩ := RD.sload r38 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r43⟩ := RD.sstore r42 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.dup11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.dup11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := RD.genMload r50 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r55⟩ := RD.sload r54 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r59⟩ := RD.sstore r58 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := r62.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5519)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5382_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5382) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5519) (morphoCreation_block_5382_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (morphoCreation_block_5382_memory (mem := mem) (x4 := x4) (x6 := x6) (x7 := x7)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))) (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960)) (UInt256.land (memLoad x5 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) x3))) ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) + (UInt256.ofNat 1)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))) (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner σ ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)) (UInt256.land (UInt256.ofNat ee.header.timestamp) x0))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960)) (UInt256.land (memLoad x5 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) x3))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord x7 (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) (UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960)) (UInt256.land (memLoad (x5 + x6) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x4.toByteArray.write 0 mem x7.toNat 32) x6.toNat 32) x6.toNat 32)) x3))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := morphoCreation_block_5382 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5519`. -/
def morphoCreation_block_5519_stack {mem : ByteArray} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad (x10 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x10 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x10 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x10 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: (UInt256.ofNat 1461501637330902918203684832716283019655932542975) :: x10 :: (UInt256.ofNat 128) :: (UInt256.ofNat 128) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 5234) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 160) :: (UInt256.ofNat 77930571974472193577215730001454066985566282397930517691434906231634542363564) :: x9 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `morphoCreation_block_5519`. -/
def morphoCreation_block_5519_memory {mem : ByteArray} {x10 : UInt256} : ByteArray :=
  ((UInt256.land (memLoad (x10 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x10 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 ((UInt256.land (memLoad x10 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5519. -/
theorem morphoCreation_block_5519 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5519) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5644) (morphoCreation_block_5519_stack (mem := mem) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (morphoCreation_block_5519_memory (mem := mem) (x10 := x10)) (M (M (M (M (M (M (M (M (M aw (x10 + x0) (⟨32⟩ : UInt256)) x7 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (x10 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x10 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) x3) (UInt256.land (memLoad (x10 + x0) mem) x1))) (x6 + (UInt256.ofNat 3)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) x3) (UInt256.land (memLoad (x10 + x0) mem) x1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x6 + (UInt256.ofNat 3)) (⟨0⟩ : UInt256))) x3) (UInt256.land (memLoad x7 mem) x8))) (x6 + x5) (memLoad x4 mem)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r7⟩ := RD.sload r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r26⟩ := RD.sstore r25 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := RD.genMload r26 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r30⟩ := RD.sstore r29 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.pushConst (UInt256.ofNat 77930571974472193577215730001454066985566282397930517691434906231634542363564) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := RD.genMload r34 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 5234) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := RD.genMload r44 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := RD.genMstore r47 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := RD.genMload r52 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := RD.genMstore r57 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := RD.genMload r62 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5644)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5519_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5519) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5644) (morphoCreation_block_5519_stack (mem := mem) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (morphoCreation_block_5519_memory (mem := mem) (x10 := x10)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) x3) (UInt256.land (memLoad (x10 + x0) mem) x1))) (x6 + (UInt256.ofNat 3)) (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) x3) (UInt256.land (memLoad (x10 + x0) mem) x1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x6 + (UInt256.ofNat 3)) (⟨0⟩ : UInt256))) x3) (UInt256.land (memLoad x7 mem) x8))) (x6 + x5) (memLoad x4 mem)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := morphoCreation_block_5519 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5644`. -/
def morphoCreation_block_5644_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `morphoCreation_block_5644`. -/
def morphoCreation_block_5644_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} : ByteArray :=
  ((memLoad (x2 + x3) ((UInt256.land (memLoad (x2 + (UInt256.ofNat 96)) (x0.toByteArray.write 0 mem (x5 + (UInt256.ofNat 64)).toNat 32)) x1).toByteArray.write 0 (x0.toByteArray.write 0 mem (x5 + (UInt256.ofNat 64)).toNat 32) (x5 + (UInt256.ofNat 96)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x2 + (UInt256.ofNat 96)) (x0.toByteArray.write 0 mem (x5 + (UInt256.ofNat 64)).toNat 32)) x1).toByteArray.write 0 (x0.toByteArray.write 0 mem (x5 + (UInt256.ofNat 64)).toNat 32) (x5 + (UInt256.ofNat 96)).toNat 32) (x5 + x4).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5644. -/
theorem morphoCreation_block_5644 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains x6 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5644) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 x6 (morphoCreation_block_5644_stack (R := R)) (morphoCreation_block_5644_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5)) (M (M (M (M (M aw (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + x3) (⟨32⟩ : UInt256)) (x5 + x4) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((62) + (memExpansionCost aw (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + x3) (⟨32⟩ : UInt256)) (x5 + x4) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := RD.genMstore r12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x6 hvalid) (by evm_ov)
  exact RD.normalizeCounters r19 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5644_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains x6 = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5644) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 x6 (morphoCreation_block_5644_stack (R := R)) (morphoCreation_block_5644_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5644 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5666_taken`. -/
def morphoCreation_block_5666_taken_stack {mem : ByteArray} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x7 :: x6 :: (UInt256.land (memLoad x4 mem) x5) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5666. -/
theorem morphoCreation_block_5666_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.land (memLoad x4 mem) x5) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5247) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5666) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5247) (morphoCreation_block_5666_taken_stack (mem := mem) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M (M aw x0 x1) x4 (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((26) + (memExpansionCost aw x0 x1) + (375 + 8 * x1.toNat + 2 * 375) + (memExpansionCost (M aw x0 x1) x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genLog2 r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 5247) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 5247) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5247)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5666_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.land (memLoad x4 mem) x5) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5247) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5666) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5247) (morphoCreation_block_5666_taken_stack (mem := mem) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5666_taken hstack hperm hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5666_fallthrough`. -/
def morphoCreation_block_5666_fallthrough_stack {mem : ByteArray} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (x7 :: x6 :: (UInt256.land (memLoad x4 mem) x5) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5666. -/
theorem morphoCreation_block_5666_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.land (memLoad x4 mem) x5) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5666) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5676) (morphoCreation_block_5666_fallthrough_stack (mem := mem) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem (M (M aw x0 x1) x4 (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((26) + (memExpansionCost aw x0 x1) + (375 + 8 * x1.toNat + 2 * 375) + (memExpansionCost (M aw x0 x1) x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genLog2 r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 5247) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5676)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5666_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.land (memLoad x4 mem) x5) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5666) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5676) (morphoCreation_block_5666_fallthrough_stack (mem := mem) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5666_fallthrough hstack hperm hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5676. -/
theorem morphoCreation_block_5676 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5676) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) g s0 σ (mem.readWithPadding x4.toNat x4.toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `morphoCreation_block_5679`. -/
def morphoCreation_block_5679_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) + (UInt256.ofNat 4)) :: x0 :: (keccakWord x4 (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) :: (UInt256.ofNat 5318) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) :: x4 :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) :: x2 :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) :: x3 :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `morphoCreation_block_5679`. -/
def morphoCreation_block_5679_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} : ByteArray :=
  ((UInt256.ofNat 67087174961651252849085867703104089940080361473223925077705643131997698129920).toByteArray.write 0 ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5679. -/
theorem morphoCreation_block_5679 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 12367) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5679) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12367) (morphoCreation_block_5679_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (morphoCreation_block_5679_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4)) (M (M (M (M (M aw x4 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x4 (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 31) (C + ((93) + (memExpansionCost aw x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x4 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x4 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x4 (UInt256.ofNat 64)) + (30 + 6 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (memExpansionCost (M (M (M aw x4 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x4 (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x4 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x4 (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 3).toByteArray.write 0 (x1.toByteArray.write 0 mem x4.toNat 32) x3.toNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5318) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMstore r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := RD.genMload r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.swap6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.swap5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.pushConst (UInt256.ofNat 67087174961651252849085867703104089940080361473223925077705643131997698129920) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := RD.genMstore r25 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 12367) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 12367) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12367)) r31 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5679_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 12367) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5679) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 12367) (morphoCreation_block_5679_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (morphoCreation_block_5679_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5679 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5750`. -/
def morphoCreation_block_5750_stack {g : Sat256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((7)) + 2)).toUInt256) :: x4 :: x2 :: x3 :: (UInt256.sub x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5750. -/
theorem morphoCreation_block_5750 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5750) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5754) (morphoCreation_block_5750_stack (g := g) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 4) (C + ((9))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genGas (RD.normalizeCounters (k' := k + 3) (C' := C + ((7))) r3 (by omega) (by omega)) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5754)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5750_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5750) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5754) (morphoCreation_block_5750_stack (g := g) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5750 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 5754: call (0xf1). No RD transition is asserted. Summaries resume at pc 5755 from a fresh symbolic RD state. -/

/-- Automatically generated RD summary for bytecode block at pc 5755. -/
theorem morphoCreation_block_5755_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5380) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5755) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5380) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 5380) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 5380) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5380)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5755_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5380) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5755) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5380) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5755_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5755. -/
theorem morphoCreation_block_5755_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5755) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5761) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 5380) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5761)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5755_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5755) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5761) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5755_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5761_taken`. -/
def morphoCreation_block_5761_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5761. -/
theorem morphoCreation_block_5761_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5339) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5761) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5339) (morphoCreation_block_5761_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 5339) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 5339) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5339)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5761_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5339) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5761) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5339) (morphoCreation_block_5761_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5761_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5761_fallthrough`. -/
def morphoCreation_block_5761_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5761. -/
theorem morphoCreation_block_5761_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5761) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5765) (morphoCreation_block_5761_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 5339) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5765)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5761_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5761) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5765) (morphoCreation_block_5761_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5761_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5765. -/
theorem morphoCreation_block_5765 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5765) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) g s0 σ (mem.readWithPadding x2.toNat x2.toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `morphoCreation_block_5771_taken`. -/
def morphoCreation_block_5771_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5771. -/
theorem morphoCreation_block_5771_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5373) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5771) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5373) (morphoCreation_block_5771_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5373) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 5373) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5373)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5771_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat rdata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5373) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5771) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5373) (morphoCreation_block_5771_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5771_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5771_fallthrough`. -/
def morphoCreation_block_5771_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5771. -/
theorem morphoCreation_block_5771_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5771) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5780) (morphoCreation_block_5771_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5373) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5780)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5771_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt x1 (UInt256.ofNat rdata.size)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5771) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5780) (morphoCreation_block_5771_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5771_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5780`. -/
def morphoCreation_block_5780_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.ofNat 5358) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5780. -/
theorem morphoCreation_block_5780 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 11535) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5780) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11535) (morphoCreation_block_5780_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5358) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 11535) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11535)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5780_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 11535) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5780) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11535) (morphoCreation_block_5780_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5780 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5790_taken`. -/
def morphoCreation_block_5790_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5790. -/
theorem morphoCreation_block_5790_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5790) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 712) (morphoCreation_block_5790_taken_stack (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 712) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 712) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5790_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5790) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 712) (morphoCreation_block_5790_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5790_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5790_fallthrough`. -/
def morphoCreation_block_5790_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5790. -/
theorem morphoCreation_block_5790_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5790) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5799) (morphoCreation_block_5790_fallthrough_stack (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 712) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5799)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5790_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub (x1 + x0) x1) x2) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5790) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5799) (morphoCreation_block_5790_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5790_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `morphoCreation_block_5799`. -/
def morphoCreation_block_5799_stack {tail : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail).size) :: (UInt256.ofNat (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail).size) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5799. -/
theorem morphoCreation_block_5799 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5333) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5799) R mem aw rdata σ k C)
    : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5333) (morphoCreation_block_5799_stack (tail := tail) (R := R)) mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode.size = 16055 := by native_decide
  have r1 := r0.codesize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 5333) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 5333) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5333)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem morphoCreation_block_5799_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode 0).contains (UInt256.ofNat 5333) = true)
    (h : RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5799) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Morpho.MorphoBlue.morphoCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 5333) (morphoCreation_block_5799_stack (tail := tail) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (morphoCreation_block_5799 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end morphoCreationBlocks
