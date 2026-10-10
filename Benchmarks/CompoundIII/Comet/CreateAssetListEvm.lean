import Benchmarks.CompoundIII.Comet.CreateAssetListHead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCreateAssetListStep {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {c : ConstructorConfig} {ptr i : Nat} {factory : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : ConstructorDataMemory c mem)
    (hn : c.assetConfigs.length ≤ 24) (hi : i < c.assetConfigs.length)
    (hlo : constructorAssetFree c c.assetConfigs.length ≤ ptr)
    (hp : ptr + 68 + 224 * c.assetConfigs.length < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1358⟩
      (createAssetListEvmStack c ptr factory i R) (createAssetListEvmMemory c mem ptr i)
      aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1358⟩
      (createAssetListEvmStack c ptr factory (i + 1) R)
      (createAssetListEvmMemory c mem ptr (i + 1)) aw' rdata σ k' C' := by
  have hs : (UInt256.ofNat (constructorAssetFree c i)).toNat = constructorAssetFree c i := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    change _ < 2^256
    omega
  have hd : (UInt256.ofNat (ptr + 68 + 224 * i)).toNat = ptr + 68 + 224 * i :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hdata := createAssetListEvmMemory_data (i := i) hm hlo (by omega)
  have hread (j : Nat) (hj : j < 7) :
      memLoad (UInt256.ofNat (constructorAssetFree c i) + UInt256.ofNat (32 * j))
        (createAssetListEvmMemory c mem ptr i) = c.assetConfigs[i].word j := by
    rw [u256_ofNat_add_eq (show constructorAssetFree c i + 32 * j < UInt256.size by
      unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
      change _ < 2^256
      omega)]
    exact hdata.assetField hi hn hj
  obtain ⟨aw1, k1, C1, r1⟩ := cometWithExtendedAssetListCreation_block_1358_taken_packed
    (by change R.length + 5 + 4 ≤ 1024; omega) (by
      rw [ult_one (by
        rw [UInt256.toNat_ofNat_of_lt (show i < UInt256.size by change _ < 2^256; omega),
          UInt256.toNat_ofNat_of_lt (show c.assetConfigs.length < UInt256.size by
            change _ < 2^256; omega)]
        exact hi)]
      decide) (by native_decide) h
  have hsbound : constructorAssetFree c i + 224 ≤
      constructorAssetFree c c.assetConfigs.length := by unfold constructorAssetFree; omega
  obtain ⟨aw2, k2, C2, r2⟩ := cometCreateAssetListEncodeAsset
    (src := UInt256.ofNat (constructorAssetFree c i)) (a := c.assetConfigs[i]) hstack
    (by rw [hs]; unfold constructorAssetFree constructorArrayEnd constructorArrayBase
          constructorRecordBase; omega)
    (by rw [hs]; exact le_trans hsbound hdata.present) (by rw [hs, hd]; omega)
    (by rw [hd]; change _ < 2^256; omega) (hdata.assetEntry hi hn) hread r1
  rw [hd, show UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) from
      u256_one_add_ofNat i,
    u256_ofNat_add_eq (show constructorAssetEntry c i + 32 < UInt256.size by
      unfold constructorAssetEntry constructorArrayBase constructorRecordBase
      change _ < 2^256
      omega),
    u256_ofNat_add_eq (show ptr + 68 + 224 * i + 224 < UInt256.size by
      change _ < 2^256; omega)] at r2
  have he : constructorAssetEntry c i + 32 = constructorAssetEntry c (i + 1) := by
    unfold constructorAssetEntry
    omega
  have hdnext : ptr + 68 + 224 * i + 224 = ptr + 68 + 224 * (i + 1) := by omega
  rw [he, hdnext] at r2
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [createAssetListEvmStack, createAssetListEvmMemory, dif_pos hi] using r2

theorem cometCreateAssetListLoop {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {c : ConstructorConfig} {ptr i : Nat} {factory : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : ConstructorDataMemory c mem)
    (hn : c.assetConfigs.length ≤ 24) (hi : i ≤ c.assetConfigs.length)
    (hlo : constructorAssetFree c c.assetConfigs.length ≤ ptr)
    (hp : ptr + 68 + 224 * c.assetConfigs.length < 2^64)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1358⟩
      (createAssetListEvmStack c ptr factory i R) (createAssetListEvmMemory c mem ptr i)
      aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1367⟩
      (createAssetListEvmStack c ptr factory c.assetConfigs.length R)
      (createAssetListEvmMemory c mem ptr c.assetConfigs.length) aw' rdata σ k' C' := by
  induction hremaining : c.assetConfigs.length - i generalizing i aw k C with
  | zero =>
    have he : i = c.assetConfigs.length := by omega
    subst i
    obtain ⟨aw', k', C', h'⟩ := cometWithExtendedAssetListCreation_block_1358_fallthrough_packed
      (by change R.length + 5 + 4 ≤ 1024; omega) (ult_zero (Nat.le_refl _)) h
    exact ⟨aw', k', C', h'⟩
  | succ remaining ih =>
    obtain ⟨aw', k', C', h'⟩ := cometCreateAssetListStep hstack hm hn (by omega) hlo hp h
    exact ih (by omega) h' (by omega)

theorem cometCreateAssetListReady {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {c : ConstructorConfig} {ptr : Nat} {factory : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hp : ptr + 68 + 224 * c.assetConfigs.length < 2^64)
    (hfactory : factory.toNat < 2^160)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1367⟩
      (createAssetListEvmStack c ptr factory c.assetConfigs.length R)
      (createAssetListEvmMemory c mem ptr c.assetConfigs.length) aw rdata σ k C) :
    ∃ k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1393⟩
      ((g.subNat C').toUInt256 :: factory :: UInt256.ofNat 0 :: UInt256.ofNat ptr ::
        UInt256.ofNat (68 + 224 * c.assetConfigs.length) :: UInt256.ofNat ptr ::
        UInt256.ofNat 32 :: UInt256.ofNat ptr :: R)
      (createAssetListEvmMemory c mem ptr c.assetConfigs.length) aw rdata σ k' C' := by
  have hclean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      factory = factory := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hfactory
  have hlen : UInt256.sub (UInt256.ofNat (ptr + 68 + 224 * c.assetConfigs.length))
      (UInt256.ofNat ptr) = UInt256.ofNat (68 + 224 * c.assetConfigs.length) := by
    apply u256_inj
    rw [usub_ofNat_lit_toNat (by omega) (by change _ < 2^256; omega),
      UInt256.toNat_ofNat_of_lt (show 68 + 224 * c.assetConfigs.length < UInt256.size by
        change _ < 2^256; omega)]
    omega
  have r := cometWithExtendedAssetListCreation_block_1367
    (by change R.length + 1 + 9 ≤ 1024; omega) h
  simp only [cometWithExtendedAssetListCreation_block_1367_stack, hclean, hlen] at r
  exact ⟨_, _, r⟩

end Benchmarks.CompoundIII.Comet
