import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEnableRuntime

/-! Copying the withdrawal queue into event memory and continuing the cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapEventLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i : Nat}
    {len src dst slot cap id ret free : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 11 ≤ 1024)
    (hperm : I.perm = true) (hdiff : len.toNat = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨13813⟩
      ([UInt256.ofNat i, len, src, dst, slot, cap, id, ret, free] ++ R)
      mem aw out σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) I g s0 ⟨13576⟩
      ([id, cap, id, ret, slot] ++ R) mem' aw' out σ k' C' := by
  induction remaining generalizing mem aw k C i src dst with
  | zero =>
      have hi : UInt256.ofNat i = len := by
        rw [show i = len.toNat by omega, u256_ofNat_toNat]
      rw [hi] at rd
      have h1 := metaMorphoV1_1_block_13813_fallthrough
        (immWords := wordsOf (immStore v))
        (by change (_ :: _ :: _ :: _ :: _ :: _ :: _ :: R).length + 4 ≤ 1024
            simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
      obtain ⟨aw', k', C', h2⟩ := metaMorphoV1_1_block_13821_packed
        (immWords := wordsOf (immStore v))
        (by simpa using (show R.length + 10 ≤ 1024 by omega)) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact ⟨mem, aw', k', C', h2⟩
  | succ n ih =>
      have hlen : len.toNat < UInt256.size := len.val.isLt
      have hi : (UInt256.ofNat i).toNat < len.toNat := by
        rw [ulit_toNat' i (by omega)]; omega
      have h1 := metaMorphoV1_1_block_13813_taken (immWords := wordsOf (immStore v))
        (by change (_ :: _ :: _ :: _ :: _ :: _ :: _ :: R).length + 4 ≤ 1024
            simp only [List.length_cons]; omega)
        (by rw [ult_one hi]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw', k', C', h2⟩ := metaMorphoV1_1_block_13872_packed
        (immWords := wordsOf (immStore v))
        (by change (_ :: _ :: _ :: _ :: _ :: R).length + 6 ≤ 1024
            simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
        u256_one_add_ofNat i
      simp only [metaMorphoV1_1_block_13872_stack, hadd] at h2
      exact ih (by omega) h2

theorem setCapEventRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {cap id ret slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13750⟩
      ([cap, id, ret, slot] ++ R) mem aw out σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) I g s0 ⟨13576⟩
      ([id, cap, id, ret, slot] ++ R) mem' aw' out σ k' C' := by
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_13750_packed
    (immWords := wordsOf (immStore v))
    (by simpa using (show R.length + 9 ≤ 1024 by omega)) rd
  exact setCapEventLoop v (codeOwnerStorageWord I σ ⟨21⟩).toNat
    hstack hperm (i := 0) (Nat.zero_add _).symm h

end Benchmarks.Morpho.MetaMorphoV1_1
