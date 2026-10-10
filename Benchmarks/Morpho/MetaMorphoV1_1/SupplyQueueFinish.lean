import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueWriteLoop
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStorePrepare

/-! Event-data copying and the successful terminal of supply-queue replacement. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem supplyQueueEventLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i : Nat}
    {len src free dst : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 9 ≤ 1024)
    (hperm : I.perm = true) (hdiff : len.toNat = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨10142⟩
      ([UInt256.ofNat i, len, src, free, dst] ++ R) mem aw out σ k C) :
    RDret (deployedRuntime v) g s0 σ ByteArray.empty := by
  induction remaining generalizing mem aw k C i src dst with
  | zero =>
      have hi : UInt256.ofNat i = len := by
        rw [show i = len.toNat by omega, u256_ofNat_toNat]
      rw [hi] at rd
      have h1 := metaMorphoV1_1_block_10142_fallthrough
        (immWords := wordsOf (immStore v))
        (by change (_ :: _ :: _ :: R).length + 4 ≤ 1024
            simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
      exact metaMorphoV1_1_block_10150 (immWords := wordsOf (immStore v)) hstack hperm h1
  | succ n ih =>
      have hlen : len.toNat < UInt256.size := len.val.isLt
      have hi : (UInt256.ofNat i).toNat < len.toNat := by
        rw [ulit_toNat' i (by omega)]; omega
      have h1 := metaMorphoV1_1_block_10142_taken (immWords := wordsOf (immStore v))
        (by change (_ :: _ :: _ :: R).length + 4 ≤ 1024
            simp only [List.length_cons]; omega)
        (by rw [ult_one hi]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      have h2 := metaMorphoV1_1_block_10190 (immWords := wordsOf (immStore v))
        (by change R.length + 7 ≤ 1024; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
        u256_one_add_ofNat i
      simp only [metaMorphoV1_1_block_10190_stack, hadd] at h2
      exact ih (by omega) h2

theorem supplyQueueFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk data : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hc : WordArrayCalldataChecks I.calldata) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨10119⟩
      ([junk, data, UInt256.ofNat (calldataArrayLength I.calldata),
        UInt256.ofNat (calldataArrayOffset I.calldata + 36)] ++ R) mem aw out σ k C) :
    RDret (deployedRuntime v) g s0 σ ByteArray.empty := by
  have h1 := metaMorphoV1_1_block_10119 (immWords := wordsOf (immStore v))
    (by change R.length + 7 ≤ 1024; omega) rd
  apply supplyQueueEventLoop v (calldataArrayLength I.calldata) hstack hperm (i := 0) ?_ h1
  rw [ulit_toNat' _ (lt_of_le_of_lt hc.length (by decide))]
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
