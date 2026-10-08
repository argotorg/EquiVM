import Benchmarks.CompoundIII.Comet.PackedGetter
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometReturnUint128Pair {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {a b : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128)
    (hmem : mem.size = 96)
    (h : RD (deployedRuntime v) ee g s0 ⟨2463⟩
      (⟨128⟩ :: a :: b :: ⟨2570⟩ :: ⟨128⟩ :: ⟨128⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (a.toByteArray ++ b.toByteArray) := by
  have rd1 := cometWithExtendedAssetList_block_2463 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have rd2 := cometWithExtendedAssetList_block_2570 (immWords := wordsOf (immStore v))
    (by omega) rd1
  unfold cometWithExtendedAssetList_block_2463_memory at rd2
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := rfl
  rw [hmask] at rd2
  have hclean : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a = a := by
    rw [u256_land_comm]
    exact low128_clean a ha
  rw [hclean] at rd2
  change RDret _ _ _ _
    ((low128 b).toByteArray.write 0 (solcScratchReturnMem mem a) 160 32
      |>.readWithPadding 128 64) at rd2
  rw [low128_clean b hb] at rd2
  exact (scratchPairReturnData a b hmem) ▸ rd2

end Benchmarks.CompoundIII.Comet
