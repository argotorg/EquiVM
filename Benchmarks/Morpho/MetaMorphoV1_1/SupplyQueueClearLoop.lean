import Benchmarks.Morpho.MetaMorphoV1_1.CountedStorageStep
import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_050
import Reasoning.StorageLoops

/-! Counted cleanup of old supply-queue entries, including unreachable enormous lengths. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

-- The generated summary hides both counters. This version retains the loop's progress.
theorem supplyQueueClearIteration {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x0 x1 : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (rd : RD (deployedRuntime v) ee g s0 ⟨10294⟩ (x0 :: x1 :: R)
      mem aw rdata σ k C) :
    ∃ C', C + 30 ≤ C' ∧ RD (deployedRuntime v) ee g s0 ⟨10280⟩
      ((UInt256.ofNat 1 + x0) :: x1 :: R) mem aw rdata
      (sstoreAccountMap ee.codeOwner σ (x0 + x1) ⟨0⟩) (k + 10) C' := by
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf
      (immStore v), (⟨10294⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf
      (immStore v), (⟨10295⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf
      (immStore v), (⟨10296⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf
      (immStore v), (⟨10297⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf
      (immStore v), (⟨10298⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  obtain ⟨C6, hC6, r6⟩ := rdSstoreCounted r5 hperm (by
    immutable_decode(immutableLayout,
      metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨10299⟩ : UInt256), UInt8.ofNat 85, .SSTORE,
      none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout,
      metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨10300⟩ : UInt256), UInt8.ofNat 96, .Push
      .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r8 := r7.add (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf
      (immStore v), (⟨10302⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 10280) (by
    immutable_decode(immutableLayout,
      metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨10303⟩ : UInt256), UInt8.ofNat 97, .Push
      .PUSH2, some ((UInt256.ofNat 10280), 2), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.jump (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf
      (immStore v), (⟨10306⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) (by
      evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10280)) r10 (by native_decide)
  exact ⟨_, by omega, RD.normalizeCounters rFinal (by omega) rfl⟩

theorem supplyQueueClearLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i : Nat}
    {start count : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 6 ≤ 1024)
    (hperm : I.perm = true) (hdiff : count.toNat = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨10280⟩
      ([UInt256.ofNat i, start, count] ++ R) mem aw out σ k C) :
    ∃ k' C', C + 40 * remaining ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨10288⟩ ([count, start, count] ++ R) mem aw out
        (clearDataWordsForwardFrom I.codeOwner σ start (UInt256.ofNat i) remaining) k' C' := by
  induction remaining generalizing i σ k C with
  | zero =>
      have hi : UInt256.ofNat i = count := by
        rw [show i = count.toNat by omega, u256_ofNat_toNat]
      rw [hi] at rd
      have h1 := metaMorphoV1_1_block_10280_fallthrough
        (immWords := wordsOf (immStore v))
        (by change R.length + 5 ≤ 1024; omega) (ult_zero (le_refl _)) rd
      exact ⟨_, _, by omega, h1⟩
  | succ n ih =>
      have hi : i < count.toNat := by omega
      have hcount : count.toNat < UInt256.size := count.val.isLt
      have hfit : i + 1 < UInt256.size := by omega
      have hword : (UInt256.ofNat i).toNat < count.toNat := by
        rw [ulit_toNat' i (by omega)]; exact hi
      have h1 := metaMorphoV1_1_block_10280_taken
        (immWords := wordsOf (immStore v))
        (by change R.length + 5 ≤ 1024; omega) (by rw [ult_one hword]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨C2, hC2, h2⟩ := supplyQueueClearIteration v
        (by change (count :: R).length + 5 ≤ 1024
            simpa only [List.length_cons, Nat.add_assoc] using hstack) hperm h1
      have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
        u256_one_add_ofNat i
      rw [hadd, u256_add_comm (UInt256.ofNat i) start] at h2
      obtain ⟨k3, C3, hC3, h3⟩ := ih (by omega) h2
      refine ⟨k3, C3, by omega, ?_⟩
      simpa only [clearDataWordsForwardFrom, u256_one_add_ofNat] using h3

theorem supplyQueueClearLoopHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {start count : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hperm : I.perm = true) (hcount : 2 ^ 251 - 30 ≤ count.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨10280⟩
      ([⟨0⟩, start, count] ++ R) mem aw out σ k C) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  obtain ⟨k', C', hC, h⟩ := supplyQueueClearLoop v count.toNat hstack hperm
    (i := 0) (by omega) rd
  apply h.oog_of_cost_gt
  have hg : g.toNat < UInt256.size := g.isLt
  have hsize : UInt256.size < 40 * (2 ^ 251 - 30) := by decide
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
