import Benchmarks.CompoundIII.Comet.ConstructorAssetsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem cometConstructorAssetsCall {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {σ : AccountMap} {c : ConstructorConfig} {out feed factoryOut : ByteArray}
    {w aw : UInt256} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hn : c.assetConfigs.length ≤ 24) (hout : out.size < UInt256.size)
    (hfeed : feed.size < UInt256.size) (hfactory : factoryOut.size < 2^138)
    (hcanon : (calldataWord factoryOut 0).toNat < 2^160)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1308⟩
      (UInt256.ofNat 640 :: UInt256.ofNat (constructorRecordBase c) ::
        calldataWord factoryOut 0 :: R)
      (constructorAssetsBaseMemory c w out feed factoryOut) aw factoryOut σ k C) :
    ∃ evm' σ' z assetOut aw' k' C',
      callViaEVM evm (AccountAddress.ofUInt256 (calldataWord factoryOut 0)) 0
        (createAssetListPayload c.assetConfigs c.assetConfigs.length) (z, evm', assetOut) ∧
      SourceState s0 ee σ' evm' ∧ assetOut.size < 2^138 ∧
      RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1394⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat (constructorAssetsPtr c) :: R)
        (callOutputMem (constructorAssetsInputMemory c w out feed factoryOut)
          assetOut (UInt256.ofNat (constructorAssetsPtr c)) ⟨32⟩) aw' assetOut σ' k' C' := by
  have hm := constructorAssetsBaseMemory_data (w := w) hn hout hfeed
    (show factoryOut.size < UInt256.size by change _ < 2^256; omega)
  have hp := constructorAssetsPtr_fits hn
  have hlo : constructorAssetFree c c.assetConfigs.length ≤ constructorAssetsPtr c := by
    unfold constructorAssetsPtr
    omega
  obtain ⟨aw1, k1, C1, r1⟩ := cometCreateAssetListHead (by omega) hm hn hlo (by omega)
    (constructorAssetsBaseMemory_free hn) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometCreateAssetListLoop hstack hm hn (Nat.zero_le _) hlo hp r1
  obtain ⟨k3, C3, r3⟩ := cometCreateAssetListReady (by omega) hp hcanon r2
  exact cometCreateAssetListCall (by omega) hs hperm hn hp r3

end Benchmarks.CompoundIII.Comet
