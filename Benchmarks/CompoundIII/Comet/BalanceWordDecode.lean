import Benchmarks.CompoundIII.Comet.TokenBalanceResponse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- GENERALIZES cometTokenBalanceFull: isolate the shared allocation and word decoder.
theorem cometAllocatedWordDecode {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hptr : ptr.toNat + 32 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨6982⟩
      (ptr :: ⟨32⟩ :: ⟨9678⟩ :: ⟨32⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (memLoad ptr (writeWord mem 64 (ptr + ⟨32⟩)) :: R)
      (writeWord mem 64 (ptr + ⟨32⟩)) aw' out σ k' C' := by
  obtain ⟨aw1, k1, C1, r1⟩ := cometAllocateBounded (v := v) (bound := 1)
    (by change R.length + 3 + 6 ≤ 1024; omega) (by decide) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
  rw [show allocationEnd ptr ⟨32⟩ = ptr + ⟨32⟩ from rfl] at r1
  have r2 := cometWithExtendedAssetList_block_9678 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_9546_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [word_add_sub_left]; decide) r2
  have r4 := cometWithExtendedAssetList_block_9558 (immWords := wordsOf (immStore v))
    (by omega) hret r3
  exact ⟨_, _, _, r4⟩

-- GENERALIZES cometTokenBalanceShort to every continuation of the shared decoder.
theorem cometShortWordDecode {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr dummy : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hptr : ptr.toNat + 32 < 2^64)
    (hshort : out.size < 32)
    (h : RD (deployedRuntime v) ee g s0 ⟨9693⟩ (dummy :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have r1 := cometWithExtendedAssetList_block_9693 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_9668 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨aw3, k3, C3, r3⟩ := cometAllocateBounded (v := v) (bound := 1)
    (by change R.length + 2 + 6 ≤ 1024; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  have r4 := cometWithExtendedAssetList_block_9678 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_9546_taken (immWords := wordsOf (immStore v))
    (by omega)
    (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) hshort]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  exact cometRevert1410 (by change R.length + 1 + 2 ≤ 1024; omega) r5

end Benchmarks.CompoundIII.Comet
