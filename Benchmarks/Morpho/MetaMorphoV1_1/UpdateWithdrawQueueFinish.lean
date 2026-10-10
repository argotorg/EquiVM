import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueWriteLoop

/-! Event-data copying and the successful terminal of withdrawal-queue replacement. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueEventLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i : Nat}
    {len src free dst : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 9 ≤ 1024)
    (hperm : I.perm = true) (hdiff : len.toNat = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨8270⟩
      ([UInt256.ofNat i, len, src, free, dst] ++ R) mem aw out σ k C) :
    RDret (deployedRuntime v) g s0 σ ByteArray.empty := by
  induction remaining generalizing mem aw k C i src dst with
  | zero =>
      have hi : UInt256.ofNat i = len := by
        rw [show i = len.toNat by omega, u256_ofNat_toNat]
      rw [hi] at rd
      have r1 := metaMorphoV1_1_block_8270_fallthrough (immWords := wordsOf (immStore v))
        (by change (_ :: _ :: _ :: R).length + 4 ≤ 1024
            simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
      exact metaMorphoV1_1_block_8278 (immWords := wordsOf (immStore v)) hstack hperm r1
  | succ n ih =>
      have hlen : len.toNat < UInt256.size := len.val.isLt
      have hi : (UInt256.ofNat i).toNat < len.toNat := by
        rw [ulit_toNat' i (by omega)]; omega
      have r1 := metaMorphoV1_1_block_8270_taken (immWords := wordsOf (immStore v))
        (by change (_ :: _ :: _ :: R).length + 4 ≤ 1024
            simp only [List.length_cons]; omega)
        (by rw [ult_one hi]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := metaMorphoV1_1_block_8318 (immWords := wordsOf (immStore v))
        (by change R.length + 7 ≤ 1024; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
      have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
        u256_one_add_ofNat i
      simp only [metaMorphoV1_1_block_8318_stack, hadd] at r2
      exact ih (by omega) r2

theorem updateWithdrawQueueFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b c ptr data : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨8243⟩
      (a :: b :: c :: ptr :: data :: R) mem aw out σ k C) :
    RDret (deployedRuntime v) g s0 σ ByteArray.empty := by
  have r1 := metaMorphoV1_1_block_8243 (immWords := wordsOf (immStore v)) (by omega) rd
  exact updateWithdrawQueueEventLoop v _ hstack hperm (i := 0) (Nat.zero_add _).symm r1

end Benchmarks.Morpho.MetaMorphoV1_1
