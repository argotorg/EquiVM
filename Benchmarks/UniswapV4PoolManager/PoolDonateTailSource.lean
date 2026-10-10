import Benchmarks.UniswapV4PoolManager.PoolDonateGrowthSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolDonateTailSource {f : Frame} {evm : State} {id amount0 amount1 liquidity delta : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "state" = some (poolRefValue id))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta))) :
    ∃ f', ExecBlock config f evm (poolDonateFunction.body.drop 7)
      (if (amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false then .staticViolation else
        .returned f' (poolDonateStep (poolDonateStep evm id false amount0 liquidity) id true amount1 liquidity)
          (some [.int (EVM.signed delta)])) := by
  have hg0 := poolDonateGrowthSource (evm := evm) false hf hs h0 hl
  by_cases hbad0 : amount0 ≠ ⟨0⟩ ∧ evm.executionEnv.perm = false
  · rw [if_pos hbad0] at hg0
    refine ⟨f, ?_⟩
    rw [if_pos (show (amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false from ⟨Or.inl hbad0.1, hbad0.2⟩)]
    exact ExecBlock.consStatic hg0
  rw [if_neg hbad0] at hg0
  let f1 := poolDonateGrowthFrame f false amount0 liquidity
  let p1 := poolDonateStep evm id false amount0 liquidity
  have hf1 : f1.contract = contract := (poolDonateGrowthFrame_contract ..).trans hf
  have hs1 : f1.locals.get? "state" = some (poolRefValue id) :=
    (poolDonateGrowthFrame_get _ _ _ _ _ (by decide)).trans hs
  have ha1 : f1.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)) :=
    (poolDonateGrowthFrame_get _ _ _ _ _ (by decide)).trans h1
  have hl1 : f1.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)) :=
    (poolDonateGrowthFrame_get _ _ _ _ _ (by decide)).trans hl
  have hd1 : f1.locals.get? "delta" = some (.int (EVM.signed delta)) :=
    (poolDonateGrowthFrame_get _ _ _ _ _ (by decide)).trans hd
  have hg1 := poolDonateGrowthSource (f := f1) (evm := p1) true hf1 hs1 ha1 hl1
  have henv : p1.executionEnv = evm.executionEnv := poolDonateStep_executionEnv ..
  rw [henv] at hg1
  by_cases hbad1 : amount1 ≠ ⟨0⟩ ∧ evm.executionEnv.perm = false
  · rw [if_pos hbad1] at hg1
    refine ⟨f, ?_⟩
    rw [if_pos (show (amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false from ⟨Or.inr hbad1.1, hbad1.2⟩)]
    exact ExecBlock.consNormal hg0 (ExecBlock.consStatic hg1)
  rw [if_neg hbad1] at hg1
  have hn : ¬((amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false) := by
    rintro ⟨h0 | h1, hp⟩
    · exact hbad0 ⟨h0, hp⟩
    · exact hbad1 ⟨h1, hp⟩
  simp only [if_neg hn]
  have hd2 : (poolDonateGrowthFrame f1 true amount1 liquidity).locals.get? "delta" = some (.int (EVM.signed delta)) :=
    (poolDonateGrowthFrame_get _ _ _ _ _ (by decide)).trans hd1
  exact ⟨_, ExecBlock.consNormal hg0 (ExecBlock.consNormal hg1 (ABlock.start.returns (evalLocalValue hd2)))⟩

end Benchmarks.UniswapV4PoolManager
