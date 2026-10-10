import Benchmarks.UniswapV4PoolManager.TickPriceSelectSource
import Benchmarks.UniswapV4PoolManager.TickPriceArithmeticSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickPriceFinishPrefix {f : Frame} {evm : EVM.State} {sqrtPrice log2 : UInt256} {oldTick : Value}
    (hs : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)))
    (hl : f.locals.get? "log_2" = some (.int (EVM.signed log2)))
    (ht : f.locals.get? "tick" = some oldTick) :
    ∃ f', ExecBlock config f evm ((tickPriceFunction.body.drop 49).take 4) (.ok f' evm) ∧
      f'.contract = f.contract ∧
      f'.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)) ∧
      f'.locals.get? "tickLow" = some (.int (EVM.signed (tickPriceLow log2))) ∧
      f'.locals.get? "tickHi" = some (.int (EVM.signed (tickPriceHigh log2))) ∧
      f'.locals.get? "tick" = some (.int (EVM.signed (tickPriceLow log2))) := by
  let low := tickPriceLow log2
  let high := tickPriceHigh log2
  let f1 : Frame := {f with locals := f.locals.insert "log_sqrt10001" (.int (EVM.signed (tickPriceScaled log2)))}
  let f2 : Frame := {f1 with locals := f1.locals.insert "tickLow" (.int (EVM.signed low))}
  let f3 : Frame := {f2 with locals := f2.locals.insert "tickHi" (.int (EVM.signed high))}
  let f4 : Frame := {f3 with locals := f3.locals.insert "tick" (.int (EVM.signed low))}
  have hl1 : f1.locals.get? "log_sqrt10001" = some (.int (EVM.signed (tickPriceScaled log2))) := store_get_self _ _ _
  have hl2 : f2.locals.get? "log_sqrt10001" = some (.int (EVM.signed (tickPriceScaled log2))) :=
    (store_get_ne _ _ (by decide : ("tickLow" == "log_sqrt10001") = false)).trans hl1
  have hlow3 : f3.locals.get? "tickLow" = some (.int (EVM.signed low)) :=
    (store_get_ne _ _ (by decide : ("tickHi" == "tickLow") = false)).trans (store_get_self _ _ _)
  have ht3 : f3.locals.get? "tick" = some oldTick :=
    (store_get_ne3 _ _ _ _ (by decide : ("log_sqrt10001" == "tick") = false)
      (by decide : ("tickLow" == "tick") = false) (by decide : ("tickHi" == "tick") = false)).trans ht
  have hp : ExecBlock config f evm ((tickPriceFunction.body.drop 49).take 4) (.ok f4 evm) :=
    ExecBlock.consNormal (tickPriceScaleSource (log2 := log2) hl)
      (ExecBlock.consNormal (tickPriceLowSource (scaled := tickPriceScaled log2) hl1)
      (ExecBlock.consNormal (tickPriceHighSource (scaled := tickPriceScaled log2) hl2) (ExecBlock.consNormal
        (ExecStmt.assign (evalLocalValue hlow3) (assignLocalValue ht3)) ExecBlock.nil)))
  have hlow4 : f4.locals.get? "tickLow" = some (.int (EVM.signed low)) :=
    (store_get_ne _ _ (by decide : ("tick" == "tickLow") = false)).trans hlow3
  have hhigh4 : f4.locals.get? "tickHi" = some (.int (EVM.signed high)) :=
    (store_get_ne _ _ (by decide : ("tick" == "tickHi") = false)).trans (store_get_self _ _ _)
  have hs4 : f4.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("log_sqrt10001" == "sqrtPriceX96") = false)
      (by decide : ("tickLow" == "sqrtPriceX96") = false)
      (by decide : ("tickHi" == "sqrtPriceX96") = false)
      (by decide : ("tick" == "sqrtPriceX96") = false)).trans hs
  have ht4 : f4.locals.get? "tick" = some (.int (EVM.signed low)) := store_get_self _ _ _
  exact ⟨f4, hp, rfl, hs4, hlow4, hhigh4, ht4⟩

theorem tickPriceFinishSourceAux {f : Frame} {evm : EVM.State} {sqrtPrice log2 low high : UInt256} {oldTick : Value}
    (hlo : tickPriceLow log2 = low) (hhi : tickPriceHigh log2 = high)
    (hf : f.contract = contract)
    (hs : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)))
    (hl : f.locals.get? "log_2" = some (.int (EVM.signed log2)))
    (ht : f.locals.get? "tick" = some oldTick) :
    ∃ f', ExecBlock config f evm (tickPriceFunction.body.drop 49)
      (signedWordResult f' evm (tickPriceChoose sqrtPrice low high)) := by
  obtain ⟨f1, hp, hc, hs1, hl1, hh1, ht1⟩ := tickPriceFinishPrefix (sqrtPrice := sqrtPrice) (log2 := log2) hs hl ht
  rw [hlo] at hl1 ht1
  rw [hhi] at hh1
  obtain ⟨f2, hselect⟩ := tickPriceSelectSource (f := f1) (sqrtPrice := sqrtPrice)
    (low := low) (high := high) (hc.trans hf) hs1 hl1 hh1 ht1
  have hparts : tickPriceFunction.body.drop 49 =
      ((tickPriceFunction.body.drop 49).take 4) ++ tickPriceFunction.body.drop 53 := by
    simpa only [List.drop_drop] using (List.take_append_drop 4 (tickPriceFunction.body.drop 49)).symm
  refine ⟨f2, ?_⟩
  rw [hparts]
  exact execBlock_append_ok hp hselect


theorem tickPriceFinishSource {f : Frame} {evm : EVM.State} {sqrtPrice log2 : UInt256} {oldTick : Value}
    (hf : f.contract = contract)
    (hs : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)))
    (hl : f.locals.get? "log_2" = some (.int (EVM.signed log2)))
    (ht : f.locals.get? "tick" = some oldTick) :
    ∃ f', ExecBlock config f evm (tickPriceFunction.body.drop 49)
      (signedWordResult f' evm (tickPriceFinish sqrtPrice log2)) := by
  simp only [tickPriceFinish_eq]
  generalize hlo : tickPriceLow log2 = low
  generalize hhi : tickPriceHigh log2 = high
  exact tickPriceFinishSourceAux (sqrtPrice := sqrtPrice) (log2 := log2)
    (low := low) (high := high) hlo hhi hf hs hl ht

end Benchmarks.UniswapV4PoolManager
