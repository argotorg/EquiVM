import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_21130`. -/
def midnight_block_21130_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 146)))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 32)) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) :: ((sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 146)))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: (x3 + (UInt256.ofNat 64)) :: ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) :: x3 :: x5 :: x2 :: R)

/-- Final memory for bytecode block summary `midnight_block_21130`. -/
def midnight_block_21130_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x3 : UInt256} {x5 : UInt256} : ByteArray :=
  ((UInt256.land ((sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 146)))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 65535)).toByteArray.write 0 ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21130. -/
theorem midnight_block_21130 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21130) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21213) (midnight_block_21130_stack (ee := ee) (mem := mem) (σ := σ) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (midnight_block_21130_memory (ee := ee) (mem := mem) (σ := σ) (x3 := x3) (x5 := x5)) (M (M (M (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (x3 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad (x3 + (UInt256.ofNat 64)) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 146)))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap4 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 146) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.not (by native_decide) (by evm_ov)
  have r26 := r25.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r27⟩ := RD.sload r26 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.or (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r31⟩ := RD.sstore r30 hperm (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r33 := r32.dup3 (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := r34.dup1 (by native_decide) (by evm_ov)
  have r36 := RD.genMload r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r40 := r39.shl (by native_decide) (by evm_ov)
  have r41 := r40.sub (by native_decide) (by evm_ov)
  have r42 := r41.and (by native_decide) (by evm_ov)
  have r43 := r42.push0 (by native_decide) (by evm_ov)
  have r44 := RD.genMstore r43 (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r47 := RD.genMstore r46 (by native_decide) (by evm_ov)
  have r48 := r47.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r49 := r48.push0 (by native_decide) (by evm_ov)
  have r50 := RD.genKeccak256 r49 (by native_decide) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r52 := RD.genMload r51 (by native_decide) (by evm_ov)
  have r53 := r52.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r54⟩ := RD.sload r53 (by native_decide) (by evm_ov)
  have r55 := r54.swap1 (by native_decide) (by evm_ov)
  have r56 := r55.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r57 := r56.dup3 (by native_decide) (by evm_ov)
  have r58 := r57.and (by native_decide) (by evm_ov)
  have r59 := r58.dup2 (by native_decide) (by evm_ov)
  have r60 := RD.genMstore r59 (by native_decide) (by evm_ov)
  have r61 := r60.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r62 := r61.dup2 (by native_decide) (by evm_ov)
  have r63 := r62.add (by native_decide) (by evm_ov)
  have r64 := r63.dup3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21213)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21130_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21130) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21213) (midnight_block_21130_stack (ee := ee) (mem := mem) (σ := σ) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) (midnight_block_21130_memory (ee := ee) (mem := mem) (σ := σ) (x3 := x3) (x5 := x5)) aw' rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 2) + (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x5.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 146)))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_21130 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21213`. -/
def midnight_block_21213_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.ofNat 224) :: (UInt256.ofNat 21305) :: x2 :: x1 :: (x2 + (UInt256.ofNat 64)) :: (x2 + (UInt256.ofNat 96)) :: (x2 + (UInt256.ofNat 128)) :: (x2 + (UInt256.ofNat 160)) :: (x2 + (UInt256.ofNat 192)) :: R)

/-- Final memory for bytecode block summary `midnight_block_21213`. -/
def midnight_block_21213_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x3 (UInt256.ofNat 96))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x3 (UInt256.ofNat 80))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x3 (UInt256.ofNat 64))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x3 (UInt256.ofNat 48))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x3 (UInt256.ofNat 32))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight x0 (UInt256.ofNat 16))).toByteArray.write 0 mem x1.toNat 32) (x2 + (UInt256.ofNat 64)).toNat 32) (x2 + (UInt256.ofNat 96)).toNat 32) (x2 + (UInt256.ofNat 128)).toNat 32) (x2 + (UInt256.ofNat 160)).toNat 32) (x2 + (UInt256.ofNat 192)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21213. -/
theorem midnight_block_21213 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21213) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_21213_stack (x1 := x1) (x2 := x2) (R := R)) (midnight_block_21213_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) (M (M (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((197) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x1 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x1 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r2 := r1.shr (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r4 := r3.and (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.dup4 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := r11.shr (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r18 := r17.dup4 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.dup5 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r23 := r22.shr (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.dup3 (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r29 := r28.dup5 (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := r30.swap3 (by native_decide) (by evm_ov)
  have r32 := r31.dup6 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r34 := r33.shr (by native_decide) (by evm_ov)
  have r35 := r34.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r36 := r35.and (by native_decide) (by evm_ov)
  have r37 := r36.dup5 (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r40 := r39.dup6 (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := r41.swap5 (by native_decide) (by evm_ov)
  have r43 := r42.dup7 (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
  have r45 := r44.shr (by native_decide) (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r47 := r46.and (by native_decide) (by evm_ov)
  have r48 := r47.dup7 (by native_decide) (by evm_ov)
  have r49 := RD.genMstore r48 (by native_decide) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r51 := r50.dup2 (by native_decide) (by evm_ov)
  have r52 := r51.add (by native_decide) (by evm_ov)
  have r53 := r52.swap7 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r55 := r54.shr (by native_decide) (by evm_ov)
  have r56 := r55.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r57 := r56.and (by native_decide) (by evm_ov)
  have r58 := r57.dup8 (by native_decide) (by evm_ov)
  have r59 := RD.genMstore r58 (by native_decide) (by evm_ov)
  have r60 := r59.push2 (UInt256.ofNat 21305) (by native_decide) (by evm_ov)
  have r61 := r60.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r62 := r61.dup3 (by native_decide) (by evm_ov)
  have r63 := r62.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r64 := r63.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21213_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21213) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_21213_stack (x1 := x1) (x2 := x2) (R := R)) (midnight_block_21213_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21213 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21305`. -/
def midnight_block_21305_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.lnot (UInt256.ofNat 1208907372870555465154560)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 281470681743360) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 32))) (UInt256.land (UInt256.lnot (UInt256.ofNat 281470681743360)) ((sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 18446462598732840960) (UInt256.shiftLeft (memLoad x3 mem) (UInt256.ofNat 48))) (UInt256.land (UInt256.lnot (UInt256.ofNat 18446462598732840960)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 281470681743360) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 32))) (UInt256.land (UInt256.lnot (UInt256.ofNat 281470681743360)) ((sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))) :: (memLoad x4 mem) :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 21305. -/
theorem midnight_block_21305 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21305) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21420) (midnight_block_21305_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 281470681743360) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 32))) (UInt256.land (UInt256.lnot (UInt256.ofNat 281470681743360)) ((sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 18446462598732840960) (UInt256.shiftLeft (memLoad x3 mem) (UInt256.ofNat 48))) (UInt256.land (UInt256.lnot (UInt256.ofNat 18446462598732840960)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 281470681743360) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 32))) (UInt256.land (UInt256.lnot (UInt256.ofNat 281470681743360)) ((sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.dup9 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.swap3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.swap2 (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.or (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r18 := r17.swap2 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push4 (UInt256.ofNat 4294901760) (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.or (by native_decide) (by evm_ov)
  have r25 := r24.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r26⟩ := RD.sstore r25 hperm (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have r28 := r27.dup7 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sload r28 (by native_decide) (by evm_ov)
  have r30 := r29.pushConst (UInt256.ofNat 281470681743360) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r31 := r30.not (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r34 := r33.swap2 (by native_decide) (by evm_ov)
  have r35 := r34.swap1 (by native_decide) (by evm_ov)
  have r36 := r35.swap2 (by native_decide) (by evm_ov)
  have r37 := r36.shl (by native_decide) (by evm_ov)
  have r38 := r37.pushConst (UInt256.ofNat 281470681743360) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r39 := r38.and (by native_decide) (by evm_ov)
  have r40 := r39.or (by native_decide) (by evm_ov)
  have r41 := r40.dup7 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r42⟩ := RD.sstore r41 hperm (by native_decide) (by evm_ov)
  have r43 := RD.genMload r42 (by native_decide) (by evm_ov)
  have r44 := r43.dup6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := RD.sload r44 (by native_decide) (by evm_ov)
  have r46 := r45.pushConst (UInt256.ofNat 18446462598732840960) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r47 := r46.not (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r50 := r49.swap2 (by native_decide) (by evm_ov)
  have r51 := r50.swap1 (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := r52.shl (by native_decide) (by evm_ov)
  have r54 := r53.pushConst (UInt256.ofNat 18446462598732840960) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r55 := r54.and (by native_decide) (by evm_ov)
  have r56 := r55.or (by native_decide) (by evm_ov)
  have r57 := r56.dup6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r58⟩ := RD.sstore r57 hperm (by native_decide) (by evm_ov)
  have r59 := RD.genMload r58 (by native_decide) (by evm_ov)
  have r60 := r59.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r61⟩ := RD.sload r60 (by native_decide) (by evm_ov)
  have r62 := r61.pushConst (UInt256.ofNat 1208907372870555465154560) (width := 10) (op := .PUSH10) (by decide) (by native_decide) (by evm_ov)
  have r63 := r62.not (by native_decide) (by evm_ov)
  have r64 := r63.and (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21420)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21305_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21305) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21420) (midnight_block_21305_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 281470681743360) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 32))) (UInt256.land (UInt256.lnot (UInt256.ofNat 281470681743360)) ((sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 18446462598732840960) (UInt256.shiftLeft (memLoad x3 mem) (UInt256.ofNat 48))) (UInt256.land (UInt256.lnot (UInt256.ofNat 18446462598732840960)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))) x8 (UInt256.lor (UInt256.land (UInt256.ofNat 281470681743360) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 32))) (UInt256.land (UInt256.lnot (UInt256.ofNat 281470681743360)) ((sstoreAccountMap ee.codeOwner σ x8 (UInt256.lor (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft (memLoad x1 mem) (UInt256.ofNat 16))) (UInt256.lor (UInt256.land (memLoad x0 mem) (UInt256.ofNat 65535)) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 4294967295)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x8 (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_21305 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21420`. -/
def midnight_block_21420_stack {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x5 :: R)

/-- Final memory for bytecode block summary `midnight_block_21420`. -/
def midnight_block_21420_memory {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  ((UInt256.ofNat 5).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad x4 mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21420. -/
theorem midnight_block_21420 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21420) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21514) (midnight_block_21420_stack (x5 := x5) (R := R)) (midnight_block_21420_memory (mem := mem) (x4 := x4)) (M (M (M (M (M aw x2 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)) x5 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80)) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 80))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80))) ((sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x5 (⟨0⟩ : UInt256)))))) x5 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 96)) (UInt256.shiftLeft (memLoad x3 mem) (UInt256.ofNat 96))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 96))) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)) x5 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80)) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 80))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80))) ((sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x5 (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x5 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 1208907372870555465154560) (width := 10) (op := .PUSH10) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.or (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sstore r9 hperm (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
  have r16 := r15.shl (by native_decide) (by evm_ov)
  have r17 := r16.not (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.swap2 (by native_decide) (by evm_ov)
  have r23 := r22.shl (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
  have r26 := r25.shl (by native_decide) (by evm_ov)
  have r27 := r26.and (by native_decide) (by evm_ov)
  have r28 := r27.or (by native_decide) (by evm_ov)
  have r29 := r28.dup4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r30⟩ := RD.sstore r29 hperm (by native_decide) (by evm_ov)
  have r31 := RD.genMload r30 (by native_decide) (by evm_ov)
  have r32 := r31.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r33⟩ := RD.sload r32 (by native_decide) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r36 := r35.shl (by native_decide) (by evm_ov)
  have r37 := r36.not (by native_decide) (by evm_ov)
  have r38 := r37.and (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r40 := r39.swap2 (by native_decide) (by evm_ov)
  have r41 := r40.swap1 (by native_decide) (by evm_ov)
  have r42 := r41.swap2 (by native_decide) (by evm_ov)
  have r43 := r42.shl (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r46 := r45.shl (by native_decide) (by evm_ov)
  have r47 := r46.and (by native_decide) (by evm_ov)
  have r48 := r47.or (by native_decide) (by evm_ov)
  have r49 := r48.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r50⟩ := RD.sstore r49 hperm (by native_decide) (by evm_ov)
  have r51 := RD.genMload r50 (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r55 := r54.shl (by native_decide) (by evm_ov)
  have r56 := r55.sub (by native_decide) (by evm_ov)
  have r57 := r56.and (by native_decide) (by evm_ov)
  have r58 := r57.push0 (by native_decide) (by evm_ov)
  have r59 := r58.swap1 (by native_decide) (by evm_ov)
  have r60 := r59.dup2 (by native_decide) (by evm_ov)
  have r61 := RD.genMstore r60 (by native_decide) (by evm_ov)
  have r62 := r61.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r63 := r62.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r64 := RD.genMstore r63 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21514)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21420_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21420) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21514) (midnight_block_21420_stack (x5 := x5) (R := R)) (midnight_block_21420_memory (mem := mem) (x4 := x4)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)) x5 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80)) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 80))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80))) ((sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x5 (⟨0⟩ : UInt256)))))) x5 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 96)) (UInt256.shiftLeft (memLoad x3 mem) (UInt256.ofNat 96))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 96))) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)) x5 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80)) (UInt256.shiftLeft (memLoad x2 mem) (UInt256.ofNat 80))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80))) ((sstoreAccountMap ee.codeOwner σ x5 (UInt256.lor (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft x1 (UInt256.ofNat 64))) x0)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x5 (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x5 (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_21420 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21514`. -/
def midnight_block_21514_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 21556) :: R)

/-- Automatically generated RD summary for bytecode block at pc 21514. -/
theorem midnight_block_21514 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 24347) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21514) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 24347) (midnight_block_21514_stack (R := R)) mem (M aw x0 (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ x1 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 112)) (UInt256.shiftLeft (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x0 (UInt256.ofNat 64) mem) (⟨0⟩ : UInt256))) (UInt256.ofNat 112))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 112))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := RD.genKeccak256 r2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.not (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := r14.swap2 (by native_decide) (by evm_ov)
  have r16 := r15.shl (by native_decide) (by evm_ov)
  have r17 := r16.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.or (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sstore r22 hperm (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 21556) (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 24347) (by native_decide) (by evm_ov)
  have r26 := r25.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 24347)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21514_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 24347) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21514) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 24347) (midnight_block_21514_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x1 (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 112)) (UInt256.shiftLeft (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord x0 (UInt256.ofNat 64) mem) (⟨0⟩ : UInt256))) (UInt256.ofNat 112))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 112))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_21514 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21556`. -/
def midnight_block_21556_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) :: (UInt256.ofNat 21583) :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_21556`. -/
def midnight_block_21556_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21556. -/
theorem midnight_block_21556 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19181) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21556) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (midnight_block_21556_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_21556_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((60) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 21583) (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.dup7 (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 19181) (by native_decide) (by evm_ov)
  have r19 := r18.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19181)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21556_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19181) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21556) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (midnight_block_21556_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_21556_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21556 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21583`. -/
def midnight_block_21583_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.sub x0 x1) :: (UInt256.ofNat 21601) :: x2 :: R)

/-- Final memory for bytecode block summary `midnight_block_21583`. -/
def midnight_block_21583_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (((UInt256.sub x0 x1) + (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21583. -/
theorem midnight_block_21583 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21583) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_21583_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (midnight_block_21583_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw x2 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((42) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.sub (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 21601) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r13 := r12.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21583_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21583) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_21583_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (midnight_block_21583_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21583 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21601`. -/
def midnight_block_21601_stack {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub ((UInt256.ofNat 32) + (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)))) (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 21662) :: (memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_21601`. -/
def midnight_block_21601_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (((UInt256.sub ((UInt256.ofNat 32) + (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)))) (memLoad (UInt256.ofNat 64) mem)) + (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 (((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32).write x1.toNat ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)).toNat) ((UInt256.ofNat 32) + (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)))).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21601. -/
theorem midnight_block_21601 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21601) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_21601_stack (mem := mem) (x0 := x0) (x2 := x2) (R := R)) (midnight_block_21601_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (Mmcopy (M (M (Mmcopy (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (x2 + (UInt256.ofNat 32)) (memLoad x2 mem)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) x1 (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32))) ((UInt256.ofNat 32) + (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)))) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 51) (C + ((148) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) + (mcopyExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (x2 + (UInt256.ofNat 32)) (memLoad x2 mem)) + (3 + 3 * (((memLoad x2 mem).toNat + 31) / 32)) + (memExpansionCost (Mmcopy (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (x2 + (UInt256.ofNat 32)) (memLoad x2 mem)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (Mmcopy (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (x2 + (UInt256.ofNat 32)) (memLoad x2 mem)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) + (mcopyExpansionCost (M (M (Mmcopy (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (x2 + (UInt256.ofNat 32)) (memLoad x2 mem)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) x1 (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32))) + (3 + 3 * (((memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)).toNat + 31) / 32)) + (memExpansionCost (Mmcopy (M (M (Mmcopy (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (x2 + (UInt256.ofNat 32)) (memLoad x2 mem)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) x1 (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32))) ((UInt256.ofNat 32) + (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (Mmcopy (M (M (Mmcopy (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (x2 + (UInt256.ofNat 32)) (memLoad x2 mem)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)) x1 (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32))) ((UInt256.ofNat 32) + (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (memLoad x0 ((⟨0⟩ : UInt256).toByteArray.write 0 (mem.write (x2 + (UInt256.ofNat 32)).toNat mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat (memLoad x2 mem).toNat) (((memLoad (UInt256.ofNat 64) mem) + (memLoad x2 mem)) + (UInt256.ofNat 32)).toNat 32)))) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.swap5 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup8 (by native_decide) (by evm_ov)
  have r18 := RD.genMcopy r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup4 (by native_decide) (by evm_ov)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  have r26 := r25.push0 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := RD.genMload r28 (by native_decide) (by evm_ov)
  have r30 := r29.swap3 (by native_decide) (by evm_ov)
  have r31 := r30.dup4 (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := RD.genMcopy r32 (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := r36.push0 (by native_decide) (by evm_ov)
  have r38 := r37.dup2 (by native_decide) (by evm_ov)
  have r39 := RD.genMstore r38 (by native_decide) (by evm_ov)
  have r40 := r39.sub (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r42 := r41.not (by native_decide) (by evm_ov)
  have r43 := r42.dup2 (by native_decide) (by evm_ov)
  have r44 := r43.add (by native_decide) (by evm_ov)
  have r45 := r44.dup3 (by native_decide) (by evm_ov)
  have r46 := RD.genMstore r45 (by native_decide) (by evm_ov)
  have r47 := r46.push2 (UInt256.ofNat 21662) (by native_decide) (by evm_ov)
  have r48 := r47.swap1 (by native_decide) (by evm_ov)
  have r49 := r48.dup3 (by native_decide) (by evm_ov)
  have r50 := r49.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r51 := r50.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r51 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21601_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21601) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_21601_stack (mem := mem) (x0 := x0) (x2 := x2) (R := R)) (midnight_block_21601_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21601 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21662`. -/
def midnight_block_21662_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x1 :: (memLoad x0 mem) :: (⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 21662. -/
theorem midnight_block_21662 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21667) (midnight_block_21662_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((12) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21667)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21662_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21667) (midnight_block_21662_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21662 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 21667: unsupported_f5 (0xf5). No RD transition is asserted. Summaries resume at pc 21668 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `midnight_block_21668_taken`. -/
def midnight_block_21668_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 21668. -/
theorem midnight_block_21668_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21745) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21668) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21745) (midnight_block_21668_taken_stack (R := R)) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 21745) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21745)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21668_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21745) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21668) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21745) (midnight_block_21668_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21668_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21668_fallthrough`. -/
def midnight_block_21668_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 21668. -/
theorem midnight_block_21668_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21668) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21682) (midnight_block_21668_fallthrough_stack (R := R)) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 21745) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21682)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21668_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21668) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21682) (midnight_block_21668_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21668_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21682`. -/
def midnight_block_21682_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: (UInt256.ofNat 21739) :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 99487468213410583139926924791468019831590502284864472083849477060402558571634) :: x1 :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_21682`. -/
def midnight_block_21682_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21682. -/
theorem midnight_block_21682 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19181) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21682) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (midnight_block_21682_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_21682_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((59) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 99487468213410583139926924791468019831590502284864472083849477060402558571634) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 21739) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.dup4 (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 19181) (by native_decide) (by evm_ov)
  have r18 := r17.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19181)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21682_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19181) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21682) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (midnight_block_21682_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_21682_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21682 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_21739`. -/
def midnight_block_21739_stack {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 21739. -/
theorem midnight_block_21739 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21739) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x6 (midnight_block_21739_stack (x5 := x5) (R := R)) mem (M aw x2 (UInt256.sub x0 x1)) rdata σ (k + 6) (C + ((18) + (memExpansionCost aw x2 (UInt256.sub x0 x1)) + (375 + 8 * (UInt256.sub x0 x1).toNat + 2 * 375))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.sub (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := RD.genLog2 r3 (by native_decide) hperm (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21739_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21739) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x6 (midnight_block_21739_stack (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_21739 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 21745. -/
theorem midnight_block_21745 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21745) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1102236863) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21760. -/
theorem midnight_block_21760 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21760) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1947410177) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21775. -/
theorem midnight_block_21775 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21775) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1275069255) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21790. -/
theorem midnight_block_21790 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21790) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 601664115) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21805. -/
theorem midnight_block_21805 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21805) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 115498757) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 21820. -/
theorem midnight_block_21820 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21820) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1025762513) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `midnight_block_21835_taken`. -/
def midnight_block_21835_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `midnight_block_21835_taken`. -/
def midnight_block_21835_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 21835. -/
theorem midnight_block_21835_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 144)) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 16904) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21835) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 16904) (midnight_block_21835_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (midnight_block_21835_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r16 := r15.shr (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 16904) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 16904)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_21835_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 144)) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 16904) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21835) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 16904) (midnight_block_21835_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (midnight_block_21835_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_21835_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end midnightBlocks
