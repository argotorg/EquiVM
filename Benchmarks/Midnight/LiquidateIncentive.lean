import Benchmarks.Midnight.LiquidateLifFrames

variable {fork : Ethereum.Fork}

/-! Paired execution of collateral selection and liquidation-incentive computation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem liquidateIncentive {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt pos dp dl receiverWord root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (he : evm.executionEnv = I) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨6477⟩
      ([maxDebt, price, pos, dp, dl, borrower, badDebt, receiverWord, mode] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (liquidateAmountsBody.take 4) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ frame' lltv lif k' C',
      ExecBlock fork config frame evm (liquidateAmountsBody.take 4) (.ok frame' evm) ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      frame'.locals.get? "lltv" = some (.int lltv.toNat) ∧
      frame'.locals.get? "lif" = some (.int lif.toNat) ∧
      TransferBudget root credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨6639⟩
        ([maxDebt, lltv, lif, price, pos, dp, dl, borrower, badDebt, receiverWord, mode] ++ R)
        mem aw rdata σ k' C' := by
  have htrace := midnightLiquidateMaxLif
    (R := [maxDebt, price, pos, dp, dl, borrower, badDebt, receiverWord, mode] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hd rd
  rw [hi] at htrace
  have hsource := liquidateMaxLifSource (fork := fork) (evm := evm)
    hf.contract hf.market hf.index [liquidateAmountsBody[3]!]
  rcases htrace with ⟨hbad, hrev⟩ | ⟨hidx, hsafe, k1, C1, hc1, rd1⟩
  · rcases hsource with ⟨_, hsrev⟩ | ⟨hi', hs', _⟩
    · exact Or.inl ⟨hsrev, hrev⟩
    · exact (hbad ⟨hi', hs'⟩).elim
  · rcases hsource with ⟨hbad, _⟩ | ⟨_, _, hprefix⟩
    · exact (hbad ⟨hidx, hsafe⟩).elim
    · let c := m.collaterals[index.toNat]
      let maximum := maxLif c.lltv c.liquidationCursor
      let f1 := liquidateMaxLifFrame frame c.lltv c.liquidationCursor
      have hf1 : LiquidateSourceFrame f1 m id index seized repaid borrower mode receiver callback data :=
        liquidateMaxLifFrame_arguments hf
      have ha1 : LiquidateAccumulators f1 bitmap maxDebt price originalDebt badDebt :=
        liquidateMaxLifFrame_accumulators ha
      have hx1 : f1.locals.get? "_maxLif" = some (.int maximum.toNat) := by
        simp only [f1, maximum, liquidateMaxLifFrame,
          wordLocal_get_ne _ _ _ _ (show "lif" ≠ "_maxLif" by decide), wordLocal_get]
      have hl1 : f1.locals.get? "lif" = some (.int maximum.toNat) := wordLocal_get _ _ _
      have hll1 : f1.locals.get? "lltv" = some (.int c.lltv.toNat) := by
        simp only [f1, liquidateMaxLifFrame,
          wordLocal_get_ne _ _ _ _ (show "lif" ≠ "lltv" by decide),
          wordLocal_get_ne _ _ _ _ (show "_maxLif" ≠ "lltv" by decide), wordLocal_get]
      have hs1 := liquidateLifSource (fork := fork) (evm := evm) hf1.contract hf1.market hf1.mode hx1 hl1
      rw [he] at hs1
      rcases midnightLiquidateLif (R := R) (by omega) hd rd1 with
        ⟨hbad, hrev⟩ | ⟨hsafe, k2, C2, hc2, rd2⟩
      · rcases hs1 with ⟨_, hsrev⟩ | ⟨hs, _⟩
        · exact Or.inl ⟨hprefix.run (ExecBlock.consRevert hsrev), hrev⟩
        · exact (hbad hs).elim
      · rcases hs1 with ⟨hbad, _⟩ | ⟨_, hsok⟩
        · exact (hbad hsafe).elim
        · exact Or.inr ⟨_, c.lltv, _, k2, C2,
            hprefix.run (ExecBlock.consNormal hsok ExecBlock.nil),
            liquidateLifFrame_arguments hf1, liquidateLifFrame_accumulators ha1,
            liquidateLifFrame_lltv hll1, liquidateLifFrame_get hl1,
            hb.mono (by omega), rd2⟩

end Benchmarks.Midnight
