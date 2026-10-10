import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapGuards
import Benchmarks.Morpho.MetaMorphoV1_1.Uint184Cast

/-! Selecting a cap branch and entering the shared setter on a decrease. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem marketRemovalCap_bound (evm : State) (id : UInt256) :
    (marketRemovalCap evm id).toNat < 2 ^ 184 :=
  u256LandMaskToNatLtOfToNat _ _ (UInt256.toNat_ofNat_of_lt (by decide))

theorem marketRemovalCapPresent (evm : State) (id : UInt256)
    (hcap : marketRemovalCap evm id ≠ ⟨0⟩) :
    ∃ account, evm.accountMap.get? evm.executionEnv.codeOwner = some account := by
  cases ha : evm.accountMap.get? evm.executionEnv.codeOwner with
  | some account => exact ⟨account, rfl⟩
  | none =>
      apply False.elim
      apply hcap
      simp only [marketRemovalCap, marketRemovalConfigWord, Solm.EVM.storageLoad,
        State.lookupAccount, ha, Option.option]
      decide

theorem submitCapBranchChoice {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw old cap : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨9222⟩ (old :: cap :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if cap.toNat < old.toNat then ⟨9229⟩ else ⟨9247⟩) (cap :: R) mem aw out σ k' C' := by
  by_cases hd : cap.toNat < old.toNat
  · rw [if_pos hd]
    exact ⟨_, _, metaMorphoV1_1_block_9222_fallthrough (immWords := wordsOf (immStore v))
      hstack (by rw [ult_one hd]; rfl) rd⟩
  · rw [if_neg hd]
    exact ⟨_, _, metaMorphoV1_1_block_9222_taken (immWords := wordsOf (immStore v))
      hstack (by rw [ult_zero (by omega)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩

theorem submitCapDecreaseReach {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw cap params id : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hd : cap.toNat < (marketRemovalCap evm id).toNat)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨9229⟩ (cap :: params :: id :: R)
      mem aw out evm.accountMap k C) :
    cap.toNat < 2 ^ 184 ∧
    (∃ account, evm.accountMap.get? evm.executionEnv.codeOwner = some account) ∧
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨13448⟩
      ([params, id, cap, ⟨1867⟩] ++ R) mem aw out evm.accountMap k' C' := by
  have hfit := lt_trans hd (marketRemovalCap_bound evm id)
  have hp := marketRemovalCapPresent evm id (fun hz ↦ by rw [hz] at hd; exact Nat.not_lt_zero _ hd)
  have r1 := metaMorphoV1_1_block_9229 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases toUint184Runtime v (by change R.length + 3 + 5 ≤ 1024; omega)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1 with
    ⟨hover, _⟩ | ⟨_, k2, C2, r2⟩
  · omega
  · have r3 := metaMorphoV1_1_block_9241 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact ⟨hfit, hp, _, _, r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
