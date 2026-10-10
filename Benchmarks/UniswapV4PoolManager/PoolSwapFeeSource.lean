import Benchmarks.UniswapV4PoolManager.PoolSwapProtocolSource
import Benchmarks.UniswapV4PoolManager.PoolSwapGrowthSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapProtocolFrame_contract (f : Frame) (s : PoolSwapStepWords) (fee protocol amount : UInt256) :
    (poolSwapProtocolFrame f s fee protocol amount).contract = f.contract := by
  unfold poolSwapProtocolFrame
  split <;> simp only [wordLocal_contract, valueLocal_contract]

theorem poolSwapProtocolFrame_get (f : Frame) (s : PoolSwapStepWords) (fee protocol amount : UInt256) (key : Ident)
    (hd : ("delta" == key) = false) (hs : ("step" == key) = false) (ha : ("amountToProtocol" == key) = false) :
    (poolSwapProtocolFrame f s fee protocol amount).locals.get? key = f.locals.get? key := by
  unfold poolSwapProtocolFrame
  split <;> simp only [wordLocal_get, valueLocal_get, hd, hs, ha, Bool.false_eq_true, if_false]

theorem poolSwapProtocolFrame_step {f : Frame} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) (fee protocol amount : UInt256) :
    (poolSwapProtocolFrame f s fee protocol amount).locals.get? "step" =
      some (poolSwapStepValue (poolSwapProtocolStep s fee protocol)) := by
  by_cases hz : protocol = ⟨0⟩
  · simpa only [poolSwapProtocolFrame, poolSwapProtocolStep, if_pos hz] using hs
  · rw [poolSwapProtocolFrame, if_neg hz]
    exact (store_get_ne _ _ (by decide : ("amountToProtocol" == "step") = false)).trans (store_get_self _ _ _)

theorem poolSwapFeeSource {f : Frame} {evm : State}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {fee protocol amount : UInt256}
    (hf : f.contract = contract)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hfee : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hp : f.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat)))
    (ha : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat))) :
    ExecBlock config f evm ((poolSwapLoopBody.drop 16).take 2)
      (.ok (poolSwapGrowthFrame (poolSwapProtocolFrame f s fee protocol amount)
        (poolSwapProtocolStep s fee protocol) r.liquidity) evm) := by
  have hfirst := poolSwapProtocolSource (evm := evm) hs hfee hp ha
  have hsecond := poolSwapGrowthSource (evm := evm) ((poolSwapProtocolFrame_contract ..).trans hf)
    (poolSwapProtocolFrame_step hs fee protocol amount)
    ((poolSwapProtocolFrame_get f s fee protocol amount "result" (by decide) (by decide) (by decide)).trans hr)
  exact ExecBlock.consNormal hfirst (execBlock_singleton hsecond)

end Benchmarks.UniswapV4PoolManager
