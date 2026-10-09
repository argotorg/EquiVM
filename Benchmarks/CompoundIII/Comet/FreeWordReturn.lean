import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_012
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: one-word return encoding at an arbitrary free-memory pointer.
theorem freeWordReturnData (mem : ByteArray) (w : UInt256) :
    (w.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding
      (memLoad (UInt256.ofNat 64) mem).toNat 32 = w.toByteArray :=
  writeWord_sparse_read_back _ _ _

theorem cometReturnWord {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw w : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨1504⟩ (w :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ w.toByteArray := by
  have hr := cometWithExtendedAssetList_block_1504
    (immWords := wordsOf (immStore v)) hstack h
  exact freeWordReturnData mem w ▸ hr

end Benchmarks.CompoundIII.Comet
