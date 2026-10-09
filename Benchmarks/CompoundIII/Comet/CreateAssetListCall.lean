import Benchmarks.CompoundIII.Comet.CreateAssetListEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem cometCreateAssetListCall {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {σ : AccountMap} {c : ConstructorConfig} {mem rdata : ByteArray}
    {aw factory : UInt256} {ptr k C : Nat} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024) (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hn : c.assetConfigs.length ≤ 24) (hp : ptr + 68 + 224 * c.assetConfigs.length < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1393⟩
      ((g.subNat C).toUInt256 :: factory :: UInt256.ofNat 0 :: UInt256.ofNat ptr ::
        UInt256.ofNat (68 + 224 * c.assetConfigs.length) :: UInt256.ofNat ptr ::
        UInt256.ofNat 32 :: UInt256.ofNat ptr :: R)
      (createAssetListEvmMemory c mem ptr c.assetConfigs.length) aw rdata σ k C) :
    ∃ evm' σ' z out aw' k' C',
      callViaEVM evm (AccountAddress.ofUInt256 factory) 0
        (createAssetListPayload c.assetConfigs c.assetConfigs.length) (z, evm', out) ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1394⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat ptr :: R)
        (callOutputMem (createAssetListEvmMemory c mem ptr c.assetConfigs.length)
          out (UInt256.ofNat ptr) ⟨32⟩) aw' out σ' k' C' := by
  have hdec : decode (cometWithExtendedAssetListCreationBytecode ++ tail) ⟨1393⟩ =
      some (.CALL, .none) :=
    decode_append_left_of_decode _ _ _ _ _ (by native_decide)
      (by rw [cometCreationBytecode_size]; decide) (by decide)
  have hcd : (createAssetListEvmMemory c mem ptr c.assetConfigs.length).readWithPadding
      (UInt256.ofNat ptr).toNat (UInt256.ofNat (68 + 224 * c.assetConfigs.length)).toNat =
        createAssetListPayload c.assetConfigs c.assetConfigs.length := by
    rw [UInt256.toNat_ofNat_of_lt (show ptr < UInt256.size by change _ < 2^256; omega),
      UInt256.toNat_ofNat_of_lt (show 68 + 224 * c.assetConfigs.length < UInt256.size by
        change _ < 2^256; omega)]
    exact createAssetListEvmMemory_payload (Nat.le_refl _) hp
  obtain ⟨evm', σ', z, out, k', C', hc, hs', hr, ho⟩ := callBridge h hs hperm hdec hcd
    (by
      rw [createAssetListPayload_size (Nat.le_refl _)]
      exact le_trans (show 68 + 224 * c.assetConfigs.length ≤ 5444 by omega)
        (by decide : 5444 ≤ Ethereum.EVM.maxReturnDataSizeByGas))
    (by change R.length + 1 + 1 ≤ 1024; omega)
  exact ⟨evm', σ', z, out, _, k', C', hc, hs', ho, hr⟩

end Benchmarks.CompoundIII.Comet
