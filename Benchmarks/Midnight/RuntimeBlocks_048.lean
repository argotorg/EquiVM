import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_12638`. -/
def midnight_block_12638_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_12638`. -/
def midnight_block_12638_memory {mem : ByteArray} : ByteArray :=
  ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12638. -/
theorem midnight_block_12638 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12638) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12719) (midnight_block_12638_stack (mem := mem) (R := R)) (midnight_block_12638_memory (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x1 x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 480) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ x1 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.push0 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.dup2 (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.dup3 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := RD.genKeccak256 r27 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r30 := r29.dup6 (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have r33 := r32.dup4 (by native_decide) (by evm_ov)
  have r34 := RD.genMstore r33 (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := RD.genMstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.swap2 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := RD.genKeccak256 r38 (by native_decide) (by evm_ov)
  have r40 := r39.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r41 := RD.genMload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r43⟩ := RD.sload r42 (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r47 := r46.shl (by native_decide) (by evm_ov)
  have r48 := r47.sub (by native_decide) (by evm_ov)
  have r49 := r48.not (by native_decide) (by evm_ov)
  have r50 := r49.and (by native_decide) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r54 := r53.shl (by native_decide) (by evm_ov)
  have r55 := r54.sub (by native_decide) (by evm_ov)
  have r56 := r55.swap2 (by native_decide) (by evm_ov)
  have r57 := r56.swap1 (by native_decide) (by evm_ov)
  have r58 := r57.swap2 (by native_decide) (by evm_ov)
  have r59 := r58.and (by native_decide) (by evm_ov)
  have r60 := r59.or (by native_decide) (by evm_ov)
  have r61 := r60.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r62⟩ := RD.sstore r61 hperm (by native_decide) (by evm_ov)
  have r63 := r62.add (by native_decide) (by evm_ov)
  have r64 := RD.genMload r63 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12719)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12638_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12638) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12719) (midnight_block_12638_stack (mem := mem) (R := R)) (midnight_block_12638_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x1 x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.lor (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 480) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ x1 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem)).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_12638 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12719_taken`. -/
def midnight_block_12719_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: (UInt256.isZero (UInt256.isZero x0)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12719. -/
theorem midnight_block_12719_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14136) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12719) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14136) (midnight_block_12719_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14136) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14136)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12719_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14136) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12719) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14136) (midnight_block_12719_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12719_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12719_fallthrough`. -/
def midnight_block_12719_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: (UInt256.isZero (UInt256.isZero x0)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12719. -/
theorem midnight_block_12719_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12719) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12728) (midnight_block_12719_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14136) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12728)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12719_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12719) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12728) (midnight_block_12719_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12719_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12728`. -/
def midnight_block_12728_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x0 :: x1 :: x2 :: (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12728. -/
theorem midnight_block_12728 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12728) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12746) (midnight_block_12728_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((36) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.swap4 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12746)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12728_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12728) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12746) (midnight_block_12728_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12728 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12746. -/
theorem midnight_block_12746_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14113) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12746) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14113) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14113) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14113)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12746_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14113) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12746) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14113) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12746_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12746. -/
theorem midnight_block_12746_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12746) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12753) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 14113) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12753)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12746_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero x3) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12746) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12753) (x0 :: x1 :: x2 :: x3 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12746_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12753`. -/
def midnight_block_12753_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x1 :: (memLoad (UInt256.ofNat 192) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12753. -/
theorem midnight_block_12753 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12753) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12757) (midnight_block_12753_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 3) (C + ((9) + (memExpansionCost aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12757)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12753_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12753) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12757) (midnight_block_12753_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12753 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12757. -/
theorem midnight_block_12757_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x5 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14090) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12757) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14090) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup7 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 14090) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14090)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12757_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x5 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14090) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12757) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14090) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12757_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12757. -/
theorem midnight_block_12757_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x5 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12757) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12773) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup7 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 14090) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12773)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12757_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x5 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12757) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12773) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12757_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12773`. -/
def midnight_block_12773_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: x0 :: x1 :: x2 :: x3 :: x5 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 12773. -/
theorem midnight_block_12773 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12773) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12775) (midnight_block_12773_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 2) (C + ((6))) := by
  let r0 := h
  have r1 := r0.dup6 (by native_decide) (by evm_ov)
  have r2 := r1.swap5 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12775)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12773_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12773) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12775) (midnight_block_12773_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12773 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12775_taken`. -/
def midnight_block_12775_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_12775_taken`. -/
def midnight_block_12775_taken_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12775. -/
theorem midnight_block_12775_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14064) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12775) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14064) (midnight_block_12775_taken_stack (R := R)) (midnight_block_12775_taken_memory (mem := mem)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((25) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14064) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14064)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12775_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14064) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12775) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14064) (midnight_block_12775_taken_stack (R := R)) (midnight_block_12775_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12775_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12775_fallthrough`. -/
def midnight_block_12775_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_12775_fallthrough`. -/
def midnight_block_12775_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12775. -/
theorem midnight_block_12775_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12775) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12785) (midnight_block_12775_fallthrough_stack (R := R)) (midnight_block_12775_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((25) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 14064) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12785)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12775_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12775) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12785) (midnight_block_12775_fallthrough_stack (R := R)) (midnight_block_12775_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12775_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_12785`. -/
def midnight_block_12785_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 288) mem).toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12785. -/
theorem midnight_block_12785 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12785) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12792) R (midnight_block_12785_memory (mem := mem)) (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((12) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12792)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12785_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12785) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12792) R (midnight_block_12785_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12785 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12792`. -/
def midnight_block_12792_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 384) ((UInt256.ofNat 32).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) :: (UInt256.ofNat 12824) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 12838) :: (memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_12792`. -/
def midnight_block_12792_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12792. -/
theorem midnight_block_12792 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20131) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12792) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20131) (midnight_block_12792_stack (mem := mem) (R := R)) (midnight_block_12792_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((63) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
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
  have r11 := r10.push2 (UInt256.ofNat 12838) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 12824) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r18 := RD.genMload r17 (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 20131) (by native_decide) (by evm_ov)
  have r20 := r19.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20131)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12792_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20131) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12792) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20131) (midnight_block_12792_stack (mem := mem) (R := R)) (midnight_block_12792_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12792 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12824`. -/
def midnight_block_12824_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.sub x0 x1) :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `midnight_block_12824`. -/
def midnight_block_12824_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (((UInt256.sub x0 x1) + (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 mem x3.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12824. -/
theorem midnight_block_12824 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12824) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_12824_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_12824_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M aw x3 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.sub (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12824_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12824) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_12824_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_12824_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12824 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12838_taken`. -/
def midnight_block_12838_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) mem) :: (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x4 :: (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) mem))) :: (UInt256.sub x3 x2) :: (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (keccakWord x1 (memLoad x0 mem) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12838. -/
theorem midnight_block_12838_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.land (UInt256.isZero (UInt256.slt x2 (⟨0⟩ : UInt256))) (UInt256.sgt (UInt256.sub x3 x2) x3)) (UInt256.land (UInt256.slt x2 (⟨0⟩ : UInt256)) (UInt256.slt (UInt256.sub x3 x2) x3))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12838) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_12838_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) rdata σ (k + 62) (C + ((187) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) + (30 + 6 * (((memLoad x0 mem).toNat + 31) / 32)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.genMload r22 (by native_decide) (by evm_ov)
  have r24 := r23.and (by native_decide) (by evm_ov)
  have r25 := r24.swap4 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r28 := RD.genMload r27 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r37 := r36.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r38 := RD.genMload r37 (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.swap2 (by native_decide) (by evm_ov)
  have r43 := r42.push0 (by native_decide) (by evm_ov)
  have r44 := r43.dup7 (by native_decide) (by evm_ov)
  have r45 := r44.dup3 (by native_decide) (by evm_ov)
  have r46 := r45.sub (by native_decide) (by evm_ov)
  have r47 := r46.swap7 (by native_decide) (by evm_ov)
  have r48 := r47.slt (by native_decide) (by evm_ov)
  have r49 := r48.dup2 (by native_decide) (by evm_ov)
  have r50 := r49.dup8 (by native_decide) (by evm_ov)
  have r51 := r50.slt (by native_decide) (by evm_ov)
  have r52 := r51.dup2 (by native_decide) (by evm_ov)
  have r53 := r52.and (by native_decide) (by evm_ov)
  have r54 := r53.swap2 (by native_decide) (by evm_ov)
  have r55 := r54.dup8 (by native_decide) (by evm_ov)
  have r56 := r55.sgt (by native_decide) (by evm_ov)
  have r57 := r56.swap1 (by native_decide) (by evm_ov)
  have r58 := r57.iszero (by native_decide) (by evm_ov)
  have r59 := r58.and (by native_decide) (by evm_ov)
  have r60 := r59.or (by native_decide) (by evm_ov)
  have r61 := r60.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r62 := r61.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r62 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12838_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.land (UInt256.isZero (UInt256.slt x2 (⟨0⟩ : UInt256))) (UInt256.sgt (UInt256.sub x3 x2) x3)) (UInt256.land (UInt256.slt x2 (⟨0⟩ : UInt256)) (UInt256.slt (UInt256.sub x3 x2) x3))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12838) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_12838_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12838_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12838_fallthrough`. -/
def midnight_block_12838_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) mem) :: (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x4 :: (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) mem))) :: (UInt256.sub x3 x2) :: (UInt256.land (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (keccakWord x1 (memLoad x0 mem) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 12838. -/
theorem midnight_block_12838_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.land (UInt256.isZero (UInt256.slt x2 (⟨0⟩ : UInt256))) (UInt256.sgt (UInt256.sub x3 x2) x3)) (UInt256.land (UInt256.slt x2 (⟨0⟩ : UInt256)) (UInt256.slt (UInt256.sub x3 x2) x3))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12838) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12921) (midnight_block_12838_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) rdata σ (k + 62) (C + ((187) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) + (30 + 6 * (((memLoad x0 mem).toNat + 31) / 32)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (memLoad x0 mem)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.genMload r22 (by native_decide) (by evm_ov)
  have r24 := r23.and (by native_decide) (by evm_ov)
  have r25 := r24.swap4 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r28 := RD.genMload r27 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r37 := r36.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r38 := RD.genMload r37 (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.swap2 (by native_decide) (by evm_ov)
  have r43 := r42.push0 (by native_decide) (by evm_ov)
  have r44 := r43.dup7 (by native_decide) (by evm_ov)
  have r45 := r44.dup3 (by native_decide) (by evm_ov)
  have r46 := r45.sub (by native_decide) (by evm_ov)
  have r47 := r46.swap7 (by native_decide) (by evm_ov)
  have r48 := r47.slt (by native_decide) (by evm_ov)
  have r49 := r48.dup2 (by native_decide) (by evm_ov)
  have r50 := r49.dup8 (by native_decide) (by evm_ov)
  have r51 := r50.slt (by native_decide) (by evm_ov)
  have r52 := r51.dup2 (by native_decide) (by evm_ov)
  have r53 := r52.and (by native_decide) (by evm_ov)
  have r54 := r53.swap2 (by native_decide) (by evm_ov)
  have r55 := r54.dup8 (by native_decide) (by evm_ov)
  have r56 := r55.sgt (by native_decide) (by evm_ov)
  have r57 := r56.swap1 (by native_decide) (by evm_ov)
  have r58 := r57.iszero (by native_decide) (by evm_ov)
  have r59 := r58.and (by native_decide) (by evm_ov)
  have r60 := r59.or (by native_decide) (by evm_ov)
  have r61 := r60.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r62 := r61.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12921)) r62 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12838_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.land (UInt256.isZero (UInt256.slt x2 (⟨0⟩ : UInt256))) (UInt256.sgt (UInt256.sub x3 x2) x3)) (UInt256.land (UInt256.slt x2 (⟨0⟩ : UInt256)) (UInt256.slt (UInt256.sub x3 x2) x3))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12838) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12921) (midnight_block_12838_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12838_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12921`. -/
def midnight_block_12921_stack {mem : ByteArray} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 480)) :: (UInt256.ofNat 12970) :: x4 :: x5 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Final memory for bytecode block summary `midnight_block_12921`. -/
def midnight_block_12921_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x6 : UInt256} : ByteArray :=
  ((UInt256.ofNat 480).toByteArray.write 0 (x1.toByteArray.write 0 (x0.toByteArray.write 0 (x3.toByteArray.write 0 (x6.toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12921. -/
theorem midnight_block_12921 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20095) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12921) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20095) (midnight_block_12921_stack (mem := mem) (x2 := x2) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_12921_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x6 := x6)) (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 35) (C + ((109) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 12970) (by native_decide) (by evm_ov)
  have r2 := r1.swap4 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap8 (by native_decide) (by evm_ov)
  have r6 := r5.caller (by native_decide) (by evm_ov)
  have r7 := r6.dup10 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.dup10 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r14 := r13.dup9 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r18 := r17.dup8 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r22 := r21.dup7 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r27 := r26.dup7 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have r29 := RD.genMstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r31 := r30.dup6 (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.push2 (UInt256.ofNat 20095) (by native_decide) (by evm_ov)
  have r35 := r34.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20095)) r35 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12921_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20095) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12921) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20095) (midnight_block_12921_stack (mem := mem) (x2 := x2) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_12921_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12921 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_12970`. -/
def midnight_block_12970_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.ofNat 416) :: (UInt256.land (memLoad (UInt256.ofNat 128) (x1.toByteArray.write 0 ((UInt256.land (memLoad (UInt256.ofNat 160) ((UInt256.land (memLoad (UInt256.ofNat 224) ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (UInt256.ofNat 224) ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) (x3 + (UInt256.ofNat 352)).toNat 32) (x3 + (UInt256.ofNat 384)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `midnight_block_12970`. -/
def midnight_block_12970_memory {ee : ExecutionEnv} {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 ((UInt256.land (memLoad (UInt256.ofNat 160) ((UInt256.land (memLoad (UInt256.ofNat 224) ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (UInt256.ofNat 224) ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (UInt256.ofNat 480) ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 416) ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 mem (x3 + (UInt256.ofNat 192)).toNat 32) (x3 + (UInt256.ofNat 224)).toNat 32) (x3 + (UInt256.ofNat 256)).toNat 32) (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) (x3 + (UInt256.ofNat 352)).toNat 32) (x3 + (UInt256.ofNat 384)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 12970. -/
theorem midnight_block_12970 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12970) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 13067) (midnight_block_12970_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_12970_memory (ee := ee) (mem := mem) (x1 := x1) (x3 := x3)) (M (M (M (M (M (M (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((190) + (memExpansionCost aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r12 := r11.dup6 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r18 := r17.dup6 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r22 := RD.genMload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r24 := r23.dup6 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := RD.genMstore r25 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r30 := r29.shl (by native_decide) (by evm_ov)
  have r31 := r30.sub (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r33 := RD.genMload r32 (by native_decide) (by evm_ov)
  have r34 := r33.and (by native_decide) (by evm_ov)
  have r35 := r34.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r36 := r35.dup6 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r42 := r41.shl (by native_decide) (by evm_ov)
  have r43 := r42.sub (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r45 := RD.genMload r44 (by native_decide) (by evm_ov)
  have r46 := r45.and (by native_decide) (by evm_ov)
  have r47 := r46.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r48 := r47.dup6 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := RD.genMstore r49 (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r52 := r51.dup5 (by native_decide) (by evm_ov)
  have r53 := r52.add (by native_decide) (by evm_ov)
  have r54 := RD.genMstore r53 (by native_decide) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r58 := r57.shl (by native_decide) (by evm_ov)
  have r59 := r58.sub (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r61 := RD.genMload r60 (by native_decide) (by evm_ov)
  have r62 := r61.and (by native_decide) (by evm_ov)
  have r63 := r62.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r64 := r63.dup5 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13067)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_12970_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 12970) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 13067) (midnight_block_12970_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_12970_memory (ee := ee) (mem := mem) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_12970 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_13067`. -/
def midnight_block_13067_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) :: (UInt256.ofNat 128) :: (UInt256.ofNat 13223) :: (memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `midnight_block_13067`. -/
def midnight_block_13067_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x5 : UInt256} {x7 : UInt256} : ByteArray :=
  ((UInt256.ofNat 96).toByteArray.write 0 ((UInt256.ofNat 65530685186148139943160654700974242543032290443373287283358098694458470976932).toByteArray.write 0 ((UInt256.land (memLoad (UInt256.ofNat 448) ((memLoad (UInt256.ofNat 512) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)).toByteArray.write 0 ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (UInt256.ofNat 512) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)).toByteArray.write 0 ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 13067. -/
theorem midnight_block_13067 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 13067) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_13067_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (midnight_block_13067_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x5 := x5) (x7 := x7)) (M (M (M (M (M (M (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 63) (C + ((191) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) + (375 + 8 * (UInt256.sub x3 x5).toNat + 4 * 375) + (memExpansionCost (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) (UInt256.ofNat 544) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) x5 (UInt256.sub x3 x5)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.land x7 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 (x2.toByteArray.write 0 mem (x0 + x1).toNat 32) (x5 + (UInt256.ofNat 448)).toNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.add (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup6 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 85728119599629476005759388951245938408922412091434260513249924659539733299184) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 544) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.swap4 (by native_decide) (by evm_ov)
  have r24 := r23.dup1 (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.swap4 (by native_decide) (by evm_ov)
  have r28 := r27.sub (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := RD.genLog4 r29 (by native_decide) hperm (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have r33 := r32.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r34 := RD.genMload r33 (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r36 := r35.dup3 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r42 := r41.shl (by native_decide) (by evm_ov)
  have r43 := r42.sub (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r45 := RD.genMload r44 (by native_decide) (by evm_ov)
  have r46 := r45.and (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r48 := r47.dup3 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := RD.genMstore r49 (by native_decide) (by evm_ov)
  have r51 := r50.pushConst (UInt256.ofNat 65530685186148139943160654700974242543032290443373287283358098694458470976932) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r53 := r52.dup3 (by native_decide) (by evm_ov)
  have r54 := r53.add (by native_decide) (by evm_ov)
  have r55 := RD.genMstore r54 (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r57 := r56.dup2 (by native_decide) (by evm_ov)
  have r58 := RD.genMstore r57 (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 13223) (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r61 := r60.dup3 (by native_decide) (by evm_ov)
  have r62 := r61.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r63 := r62.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r63 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_13067_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 13067) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_13067_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (midnight_block_13067_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x5 := x5) (x7 := x7)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_13067 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
