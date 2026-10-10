import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStorageMatch
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_050
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Runtime copying of the replacement queue from calldata into storage. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem supplyQueueWriteLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 7 ≤ 1024)
    (hc : WordArrayCalldataChecks I.calldata) (hperm : I.perm = true)
    (hdiff : calldataArrayLength I.calldata = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨10111⟩
      ([UInt256.ofNat i, UInt256.ofNat (calldataArrayOffset I.calldata + 36 + 32 * i),
        UInt256.ofNat (calldataArrayLength I.calldata)] ++ R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨10119⟩
      ([UInt256.ofNat (calldataArrayLength I.calldata),
        UInt256.ofNat (calldataArrayOffset I.calldata + 36 + 32 * calldataArrayLength I.calldata),
        UInt256.ofNat (calldataArrayLength I.calldata)] ++ R) mem aw out
      (storeWordArray I.codeOwner σ (solidityBytesDataBaseSlot ⟨20⟩)
        (fun j ↦ calldataWord I.calldata (calldataArrayOffset I.calldata + 36 + 32 * j))
        i remaining) k' C' := by
  have hlen : calldataArrayLength I.calldata < UInt256.size :=
    lt_of_le_of_lt hc.length (by decide)
  have hdata := hc.data
  have hsize : I.calldata.size < UInt256.size := lt_trans hc.size (by decide)
  induction remaining generalizing i σ k C with
  | zero =>
      have hi : i = calldataArrayLength I.calldata := by omega
      subst i
      exact RD.pack (metaMorphoV1_1_block_10111_fallthrough
        (immWords := wordsOf (immStore v))
        (by change R.length + 5 ≤ 1024; omega) (ult_zero (le_refl _)) rd)
  | succ n ih =>
      have hi : i < calldataArrayLength I.calldata := by omega
      have hword : (UInt256.ofNat i).toNat <
          (UInt256.ofNat (calldataArrayLength I.calldata)).toNat := by
        rw [ulit_toNat' i (by omega), ulit_toNat' _ hlen]; exact hi
      have haddr : (UInt256.ofNat (calldataArrayOffset I.calldata + 36 + 32 * i)).toNat =
          calldataArrayOffset I.calldata + 36 + 32 * i := ulit_toNat' _ (by omega)
      have h1 := metaMorphoV1_1_block_10111_taken (immWords := wordsOf (immStore v))
        (by change R.length + 5 ≤ 1024; omega) (by rw [ult_one hword]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨k2, C2, h2⟩ := metaMorphoV1_1_block_10212
        (immWords := wordsOf (immStore v))
        (by change (_ :: R).length + 6 ≤ 1024; simp only [List.length_cons]; omega) hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
        (u256_add_comm _ _).trans (u256_one_add_ofNat i)
      have hstep : UInt256.ofNat (calldataArrayOffset I.calldata + 36 + 32 * i) +
          UInt256.ofNat 32 =
          UInt256.ofNat (calldataArrayOffset I.calldata + 36 + 32 * (i + 1)) := by
        apply (u256_add_comm _ _).trans
        exact (u256_32_add_ofNat _).trans (congrArg UInt256.ofNat (by omega))
      simp only [metaMorphoV1_1_block_10212_stack, hadd, hstep, haddr,
        ← supplyQueueDataBase_eq] at h2
      exact ih (by omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
