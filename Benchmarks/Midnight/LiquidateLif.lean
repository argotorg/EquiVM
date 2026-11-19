import Benchmarks.Midnight.LiquidateGrowthTrace
import Benchmarks.Midnight.LiquidateGrowthSource

/-! The mode-dependent liquidation incentive, in source and runtime execution. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateLif (mode maximum timestamp maturity : UInt256) : UInt256 :=
  if mode = ⟨0⟩ then maximum else liquidateGrownLif maximum timestamp maturity

def liquidateLifFrame (frame : Frame) (mode maximum timestamp maturity : UInt256) : Frame :=
  if mode = ⟨0⟩ then frame else liquidateGrownFrame frame
    (liquidateGrownLif maximum timestamp maturity)

def LiquidateLifSafe (mode maximum timestamp maturity : UInt256) : Prop :=
  mode ≠ ⟨0⟩ → LiquidateGrowthSafe maximum timestamp maturity

theorem liquidateLifSource {frame : Frame} {evm : State} {m : MarketData}
    {mode maximum : UInt256} (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hmode : frame.locals.get? "postMaturityMode" = some (wordToElem .bool mode))
    (hx : frame.locals.get? "_maxLif" = some (.int maximum.toNat))
    (hl : frame.locals.get? "lif" = some (.int maximum.toNat)) :
    let timestamp := UInt256.ofNat evm.executionEnv.header.timestamp
    (¬ LiquidateLifSafe mode maximum timestamp m.maturity ∧
      ExecStmt config frame evm (liquidateAmountsBody[3]!) .reverted) ∨
    (LiquidateLifSafe mode maximum timestamp m.maturity ∧
      ExecStmt config frame evm (liquidateAmountsBody[3]!)
        (.ok (liquidateLifFrame frame mode maximum timestamp m.maturity) evm)) := by
  dsimp only
  by_cases hz : mode = ⟨0⟩
  · refine Or.inr ⟨fun hn ↦ (hn hz).elim, ?_⟩
    simp only [liquidateLifFrame, if_pos hz]
    apply ExecStmt.iteFalse ?_ ExecBlock.nil
    simp only [evalExpr?, hmode, EvalResult.ofOption, wordToElemBool, hz, decide_true, Bool.not_true]
  · have hcond : evalExpr? config frame evm (.var "postMaturityMode") = .ok (.bool true) := by
      simp only [evalExpr?, hmode, EvalResult.ofOption, wordToElemBool, hz, decide_false, Bool.not_false]
    rcases liquidateGrowthSource hc hm hx hl with ⟨hbad, hrev⟩ | ⟨hsafe, hsource⟩
    · exact Or.inl ⟨fun h ↦ hbad (h hz), ExecStmt.iteTrue hcond hrev⟩
    · refine Or.inr ⟨fun _ ↦ hsafe, ?_⟩
      simpa only [liquidateLifFrame, if_neg hz] using
        (show ExecStmt config frame evm (liquidateAmountsBody[3]!)
          (.ok (liquidateGrownFrame frame (liquidateGrownLif maximum
            (UInt256.ofNat evm.executionEnv.header.timestamp) m.maturity)) evm) from
          ExecStmt.iteTrue hcond hsource)

theorem midnightLiquidateLif {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw maximum lltv maxDebt price pos dp dl borrower badDebt receiver mode : UInt256}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (rd : RD midnightBytecode I g s0 ⟨6540⟩
      ([maximum, lltv, maxDebt, price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R)
      mem aw rdata σ k C) :
    let timestamp := UInt256.ofNat I.header.timestamp
    (¬ LiquidateLifSafe mode maximum timestamp m.maturity ∧ RDrev midnightBytecode g s0) ∨
    (LiquidateLifSafe mode maximum timestamp m.maturity ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨6639⟩
        ([maxDebt, lltv, liquidateLif mode maximum timestamp m.maturity,
          price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R) mem aw rdata σ k' C') := by
  dsimp only
  by_cases hz : mode = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_6540_taken (R := R) (by omega)
      (by rw [hz]; decide) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_7414
      (R := [price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_7414_stack] at rd2
    simp only [liquidateLif, if_pos hz]
    exact Or.inr ⟨fun hn ↦ (hn hz).elim, _, _, by omega, rd2⟩
  · have rd1 := midnightBlocks.midnight_block_6540_fallthrough (R := R) (by omega)
      (isZero_eq_zero_of_ne hz) rd
    rcases midnightLiquidateGrowth
      (R := [price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hd rd1 with
      ⟨hbad, hrev⟩ | ⟨hsafe, k2, C2, hc2, rd2⟩
    · exact Or.inl ⟨fun h ↦ hbad (h hz), hrev⟩
    · refine Or.inr ⟨fun _ ↦ hsafe, k2, C2, by omega, ?_⟩
      simpa only [liquidateLif, if_neg hz] using rd2

end Benchmarks.Midnight
