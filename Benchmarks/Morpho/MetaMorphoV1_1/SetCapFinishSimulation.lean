import Benchmarks.Morpho.MetaMorphoV1_1.SetCapFrames
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEventRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_062

/-! Checked addition, total-assets storage, and event completion after the cap reader. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapFinishSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {previous assets cap id ret slot ptr : UInt256} {R : List UInt256}
    {p : MarketParamsData} (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hready : SetCapReady frame p id cap ptr)
    (hp : frame.locals.get? "previousTotalAssets" = some (uint256Value previous))
    (ha : frame.locals.get? "__c0" = some (uint256Value assets))
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12515⟩
      ([assets, previous, ⟨13745⟩, ⟨13750⟩, cap, id, ret, slot] ++ R)
      mem aw out σ k C) :
    (ExecBlock config frame evm (setCapEnableBody.drop 8) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (mem' : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧ SetCapReady frame' p id cap ptr ∧
      ExecBlock config frame evm (setCapEnableBody.drop 8) (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13576⟩
        ([id, cap, id, ret, slot] ++ R) mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12515_packed
    (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 3 ≤ 1024; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hfit : previous.toNat + assets.toNat < UInt256.size
  · obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
      (by change R.length + 5 + 4 ≤ 1024; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_13745_packed
      (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 1 ≤ 1024; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    rw [hs.accounts] at h3
    obtain ⟨aw4, k4, C4, h4⟩ := updateLastAssetsReturn v
      (evm := evm) (value := previous + assets) (ret := ⟨13750⟩)
      (R := [cap, id, ret, slot] ++ R)
      (by change R.length + 4 + 6 ≤ 1024; omega)
      (by rw [hs.env]; exact hperm)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest)
      (by rw [hs.env]; exact h3)
    rw [hs.env] at h4
    obtain ⟨mem5, aw5, k5, C5, h5⟩ := setCapEventRuntime v hstack hperm h4
    refine .inr ⟨updateLastAssetsState evm (previous + assets), setCapUpdatedFrame frame,
      mem5, ?_, hready.updated, setCapUpdateAndEmit hready.contract hready.queue hp ha hfit,
      aw5, k5, C5, h5⟩
    have h := hs.storageWrite ⟨22⟩ (previous + assets)
    rw [h.accounts] at h
    simpa only [updateLastAssetsState, hs.env] using h
  · exact .inl ⟨setCapUpdateOverflow hp ha (Nat.le_of_not_gt hfit),
      checkedAddRevert v (by change R.length + 5 + 4 ≤ 1024; omega)
        (Nat.le_of_not_gt hfit) h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
