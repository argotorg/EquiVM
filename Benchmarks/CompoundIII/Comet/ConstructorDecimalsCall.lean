import Benchmarks.CompoundIII.Comet.ConstructorDecimalsEnter
import Benchmarks.CompoundIII.Comet.ConstructorSourcePrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem constructorDecodedMemory_size (c : ConstructorConfig) :
    (constructorDecodedMemory c).size = constructorAssetFree c c.assetConfigs.length := by
  rw [constructorDecodedMemory, writeWord_sparse_size,
    constructorAssetLoopMemory_size (Nat.le_refl _)]
  split
  · rename_i hn
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase
    rw [hn]
    omega
  · unfold constructorAssetFree constructorArrayEnd constructorArrayBase
    omega

theorem constructorDecimalsMemory_payload {c : ConstructorConfig}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64) :
    (constructorDecimalsMemory c).readWithPadding
      (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)).toNat 4 = decimalsPayload := by
  rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
  have hr := toByteArray_write_read_window_of_gap
    (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224)) (constructorDecodedMemory c)
    (constructorAssetFree c c.assetConfigs.length) 0 4 (by decide) (by decide) (by decide)
    (by rw [constructorDecodedMemory_size, Nat.sub_self]; exact lt_usize 0 (by decide))
  have hsel : (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224)).toByteArray.extract
      0 (0 + 4) = decimalsPayload := by decide +kernel
  simpa only [Nat.add_zero] using hr.trans hsel

def constructorDecimalsCopyMemory (c : ConstructorConfig) (out : ByteArray) : ByteArray :=
  callOutputMem (constructorDecimalsMemory c) out
    (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)) ⟨32⟩

/-- The first constructor STATICCALL and its source-call witness use the same EVM invocation. -/
theorem cometConstructorDecimalsCall {σ σ₀ A I} {g : Sat256} {c : ConstructorConfig}
    {aw : UInt256} {k C : Nat}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
      (initState σ σ₀ g A I) ⟨733⟩
      ((g.subNat C).toUInt256 :: constructorRecordWord c 2 ::
        UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) :: ⟨4⟩ ::
        UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) :: ⟨32⟩ ::
        UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) ::
        UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorDecimalsMemory c) aw ByteArray.empty σ k C) :
    ∃ evm' σ' z out aw' k' C',
      callViaEVM (initState σ σ₀ g A I) c.baseToken 0 decimalsPayload (z, evm', out) false ∧
      SourceState (initState σ σ₀ g A I) I σ' evm' ∧
      out.size < 2^138 ∧
      RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I g
        (initState σ σ₀ g A I) ⟨734⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) ::
          UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorDecimalsCopyMemory c out) aw' out σ' k' C' := by
  have hdec : decode (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
      ⟨733⟩ = some (.STATICCALL, .none) :=
    decode_append_left_of_decode _ _ _ _ _ (by native_decide)
      (by rw [cometCreationBytecode_size]; decide) (by decide)
  obtain ⟨evm', σ', z, out, k', C', hc, hs, hr, ho⟩ := staticCallBridge h .init hdec
    (constructorDecimalsMemory_payload hfree) (by change 4 ≤ _; decide)
    (by change 12 ≤ 1024; decide)
  have haddr : AccountAddress.ofUInt256 (constructorRecordWord c 2) = c.baseToken :=
    accountAddress_roundtrip c.baseToken
  rw [haddr] at hc
  exact ⟨evm', σ', z, out, _, k', C', hc, hs, ho, hr⟩

end Benchmarks.CompoundIII.Comet
