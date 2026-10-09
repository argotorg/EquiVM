import Benchmarks.CompoundIII.Comet.ConstructorInitialImmsMemory
import Benchmarks.CompoundIII.Comet.ConstructorInitialImmsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

theorem cometConstructorInitialImms {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {σ : AccountMap} {c : ConstructorConfig} {mem rdata : ByteArray}
    {w aw : UInt256} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨902⟩
      (w :: UInt256.ofNat (constructorRecordBase c) :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨988⟩
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
        ⟨255⟩ :: w :: UInt256.ofNat (constructorRecordBase c) :: R)
      (constructorInitialImmMemory c w mem) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := cometWithExtendedAssetListCreation_block_902_packed hstack h
  exact ⟨aw', k', C', by simpa only [constructorInitialImmMemory_eq hm hsize] using hr⟩

end Benchmarks.CompoundIII.Comet
