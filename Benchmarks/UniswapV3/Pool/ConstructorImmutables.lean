import Benchmarks.UniswapV3.Pool.ConstructorModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 5000

theorem constructorFinalGet (original : AccountAddress) (out : ByteArray) :
    (constructorFinalImms original out).get? "original" = some (.address original) ∧
    (constructorFinalImms original out).get? "factory" =
      some (.address (AccountAddress.ofNat (calldataWord out 0).toNat)) ∧
    (constructorFinalImms original out).get? "token0" =
      some (.address (AccountAddress.ofNat (calldataWord out 32).toNat)) ∧
    (constructorFinalImms original out).get? "token1" =
      some (.address (AccountAddress.ofNat (calldataWord out 64).toNat)) ∧
    (constructorFinalImms original out).get? "fee" = some (.int (constructorFee out)) ∧
    (constructorFinalImms original out).get? "tickSpacing" =
      some (.int (constructorUnsignedSpacing out)) ∧
    (constructorFinalImms original out).get? "maxLiquidityPerTick" =
      some (.int (spacingLiquidity (constructorSpacing out))) := by
  simp only [constructorFinalImms, constructorSpacingImms, constructorParameterImms,
    constructorOriginalImms, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem constructorFinalFit (original : AccountAddress) (out : ByteArray) :
    immutablesFit contract (constructorFinalImms original out) := by
  obtain ⟨ho, hf, h0, h1, hfee, hs, hm⟩ := constructorFinalGet original out
  intro d hd
  change d ∈ [⟨"original", .address⟩, ⟨"factory", .address⟩, ⟨"token0", .address⟩,
    ⟨"token1", .address⟩, ⟨"fee", .int (.uint ⟨256, by decide⟩)⟩,
    ⟨"tickSpacing", .int (.uint ⟨256, by decide⟩)⟩,
    ⟨"maxLiquidityPerTick", .int (.uint ⟨256, by decide⟩)⟩] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, ho, rfl⟩
  · exact ⟨_, hf, rfl⟩
  · exact ⟨_, h0, rfl⟩
  · exact ⟨_, h1, rfl⟩
  · refine ⟨_, hfee, ?_⟩
    have hb := constructorFee_bounds out
    simp only [elemValueFits, decide_eq_true_eq]
    change 0 ≤ constructorFee out ∧ constructorFee out < 2 ^ 256
    exact ⟨hb.1, by omega⟩
  · refine ⟨_, hs, ?_⟩
    have hb := constructorUnsignedSpacing_bounds out
    simp only [elemValueFits, decide_eq_true_eq]
    change 0 ≤ constructorUnsignedSpacing out ∧ constructorUnsignedSpacing out < 2 ^ 256
    exact ⟨hb.1, by omega⟩
  · refine ⟨_, hm, ?_⟩
    have hb := spacingLiquidity_bounds (constructorSpacing out)
    simp only [elemValueFits, decide_eq_true_eq]
    change 0 ≤ spacingLiquidity (constructorSpacing out) ∧
      spacingLiquidity (constructorSpacing out) < 2 ^ 256
    exact ⟨hb.1, by omega⟩

theorem constructorFinalDeployed (original : AccountAddress) (out : ByteArray) :
    immutableLayout.deployed uniswapV3PoolBytecode (constructorFinalImms original out) =
      deployedRuntime (constructorValuation original out) := by
  obtain ⟨ho, hf, h0, h1, hfee, hs, hm⟩ := constructorFinalGet original out
  unfold deployedRuntime Layout.deployed
  apply Layout.runtime_congr
  intro site hsite
  have hk := immutableLayout_keys site hsite
  change site.2.2 ∈ ["original", "factory", "token0", "token1", "fee", "tickSpacing",
    "maxLiquidityPerTick"] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with hk | hk | hk | hk | hk | hk | hk
  · rw [hk, wordsOf_of_get ho rfl, wordsOf_immStore_original]
    rfl
  · rw [hk, wordsOf_of_get hf rfl, wordsOf_immStore_factory]
    rfl
  · rw [hk, wordsOf_of_get h0 rfl, wordsOf_immStore_token0]
    rfl
  · rw [hk, wordsOf_of_get h1 rfl, wordsOf_immStore_token1]
    rfl
  · rw [hk, wordsOf_of_get (w := EVM.wordOfInt (constructorFee out)) hfee rfl,
      wordsOf_immStore_fee, wordOfInt_ofNat_toNat]
    rfl
  · rw [hk, wordsOf_immStore_tickSpacing, wordOfInt_ofNat_toNat]
    simp only [constructorValuation]
    exact wordsOf_of_get hs rfl
  · rw [hk, wordsOf_immStore_maxLiquidityPerTick, wordOfInt_ofNat_toNat]
    simp only [constructorValuation]
    exact wordsOf_of_get hm rfl

end Benchmarks.UniswapV3.Pool
