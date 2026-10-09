import Benchmarks.Morpho.MorphoBlue.HealthyPriceReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoHealthyPriceRoutines {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw account price ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (hstack : R.length + 32 ≤ 1024) (hc : account.toNat < EVM.addressModulus)
    (hparams : p.InMemory (UInt256.ofNat 128) mem) (hsize : 288 ≤ mem.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14189)
      ([UInt256.ofNat 128, p.id, account, price, ret] ++ R) mem aw out σ k C) :
    (¬ HealthyPriceFits σ ee p account price ∧ RDrev (deployedRuntime v) g s0) ∨
    (HealthyPriceFits σ ee p account price ∧ ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      ((if healthyPriceResult σ ee p account price then UInt256.ofNat 1 else UInt256.ofNat 0) :: R)
      (healthyPriceMem p.id account mem) aw' out σ k' C') := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoHealthyPriceReachAssets (v := v) (by omega) hc h
  by_cases hf1 : AssetsUpFits (positionFieldWord σ ee p.id account 1)
      (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
  swap
  · exact .inl ⟨fun hh ↦ hf1 hh.1,
      morphoAssetsUpReverts (v := v) (by change R.length + 13 + 14 ≤ 1024; omega) hf1 rd1⟩
  obtain ⟨k2, C2, rd2⟩ := morphoAssetsUpOk (v := v) (by change R.length + 13 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf1 rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoHealthyPriceReachCollateral (v := v) (by omega) rd2
  by_cases hf2 : (positionFieldWord σ ee p.id account 2).toNat * price.toNat < UInt256.size
  swap
  · exact .inl ⟨fun hh ↦ hf2 hh.2.1,
      morphoCheckedMulReverts (v := v) (by change R.length + 7 + 6 ≤ 1024; omega) (Nat.le_of_not_gt hf2) rd3⟩
  obtain ⟨k4, C4, rd4⟩ := morphoCheckedMulOk (v := v) (by change R.length + 7 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf2 rd3
  have hpref := healthyPriceMem_prefix p.id account mem 288
  have hlltv : memLoad (UInt256.ofNat 256) (healthyPriceMem p.id account mem) = p.lltv := by
    rw [memoryPrefix_memLoad hpref (UInt256.ofNat 256) (by decide) (by decide) hsize]
    exact hparams ⟨4, by decide⟩
  have rd5 := morphoBlocks.morpho_block_14355 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  change RD _ _ _ _ _
    ([healthyCollateralValue σ ee p account price, memLoad (UInt256.ofNat 256) (healthyPriceMem p.id account mem),
      UInt256.ofNat 14365, wad, healthyBorrowed σ ee p account, ret] ++ R)
    (healthyPriceMem p.id account mem) _ _ _ _ _ at rd5
  rw [hlltv] at rd5
  by_cases hf3 : (healthyCollateralValue σ ee p account price).toNat * p.lltv.toNat < UInt256.size
  swap
  · exact .inl ⟨fun hh ↦ hf3 hh.2.2,
      morphoCheckedMulReverts (v := v) (by change R.length + 3 + 6 ≤ 1024; omega) (Nat.le_of_not_gt hf3) rd5⟩
  obtain ⟨k6, C6, rd6⟩ := morphoCheckedMulOk (v := v) (by change R.length + 3 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf3 rd5
  have rd7 := morphoBlocks.morpho_block_14365 (immWords := wordsOf (immStore v)) (by change R.length + 4 ≤ 1024; omega) hvalid rd6
  change RD _ _ _ _ _
    (UInt256.isZero (UInt256.lt (healthyMaxBorrow σ ee p account price) (healthyBorrowed σ ee p account)) :: R)
    (healthyPriceMem p.id account mem) _ _ _ _ _ at rd7
  have hw : UInt256.isZero (UInt256.lt (healthyMaxBorrow σ ee p account price) (healthyBorrowed σ ee p account)) =
      if healthyPriceResult σ ee p account price then UInt256.ofNat 1 else UInt256.ofNat 0 := by
    by_cases hb : (healthyBorrowed σ ee p account).toNat ≤ (healthyMaxBorrow σ ee p account price).toNat
    · rw [ult_zero hb]; simp only [healthyPriceResult, decide_eq_true hb, ↓reduceIte]; rfl
    · rw [ult_one (Nat.lt_of_not_ge hb)]; simp only [healthyPriceResult, decide_eq_false hb, Bool.false_eq_true, ↓reduceIte]; rfl
  rw [hw] at rd7
  exact .inr ⟨⟨hf1, hf2, hf3⟩, _, _, _, rd7⟩

end Benchmarks.Morpho.MorphoBlue
