import Benchmarks.UniswapV4PoolManager.PoolSwapResultInitSource
import Benchmarks.UniswapV4PoolManager.PoolSwapProtocolInitSource
import Benchmarks.UniswapV4PoolManager.PoolSwapSetupLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapLoadedFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolSwapParamsWords) : Frame :=
  let packed := poolSlot0Word evm id
  poolSwapResultInitFrame (poolSwapProtocolInitFrame (poolSwapInputsFrame f packed p.zeroForOne) packed p.zeroForOne)
    packed (poolLiquidityWord evm id) p.amountSpecified

theorem poolSwapLoadedSource {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) :
    ExecBlock config f evm (poolSwapFunction.body.take 18) (.ok (poolSwapLoadedFrame f evm id p) evm) := by
  let packed := poolSlot0Word evm id
  let f1 := poolSwapInputsFrame f packed p.zeroForOne
  let f2 := poolSwapProtocolInitFrame f1 packed p.zeroForOne
  have h0 := poolSwapInputsSource (evm := evm) hs hp
  have hs1 : f1.locals.get? "slot0Start" = some (wordBytes32Value packed) :=
    (store_get_ne _ _ (by decide : ("zeroForOne" == "slot0Start") = false)).trans (store_get_self _ _ _)
  have hz1 : f1.locals.get? "zeroForOne" = some (.bool p.zeroForOne) := store_get_self _ _ _
  have hf1 : f1.contract = contract := (poolSwapInputsFrame_contract f packed p.zeroForOne).trans hf
  have hf2 : f2.contract = contract := (poolSwapProtocolInitFrame_contract f1 packed p.zeroForOne).trans hf1
  have h1 := poolSwapProtocolInitSource (f := f1) (evm := evm) hf1 hs1 hz1
  have hg0 := poolSwapInputsFrame_get f packed p.zeroForOne
  have hg1 := poolSwapProtocolInitFrame_get f1 packed p.zeroForOne
  have hs2 : f2.locals.get? "self" = some (poolRefValue id) :=
    (hg1 "self" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hg0 "self" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs)
  have hp2 : f2.locals.get? "params" = some (poolSwapParamsValue p) :=
    (hg1 "params" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hg0 "params" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp)
  have hslot2 := (hg1 "slot0Start" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs1
  have hr1 : f1.locals.get? "result" = some (poolSwapResultValue poolSwapZeroResult) :=
    (store_get_ne2 _ _ _ (by decide : ("slot0Start" == "result") = false)
      (by decide : ("zeroForOne" == "result") = false)).trans (store_get_self _ _ _)
  have hr2 := (hg1 "result" (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr1
  have h2 := poolSwapResultInitSource (f := f2) (evm := evm) hf2 hs2 hp2 hslot2 hr2
  exact execBlock_append h0 (execBlock_append h1 h2)

theorem poolSwapLoadedLocals {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) :
    PoolSwapSetupLocals (poolSwapLoadedFrame f evm id p) id (poolSlot0Word evm id) p
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id)) ⟨0⟩
      (poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne) := by
  constructor
  · rw [poolSwapLoadedFrame, poolSwapResultInitFrame_contract,
      poolSwapProtocolInitFrame_contract, poolSwapInputsFrame_contract]
    exact hf
  all_goals simp only [poolSwapLoadedFrame, poolSwapResultInitFrame, poolSwapProtocolInitFrame, poolSwapInputsFrame,
    valueLocal_get, wordLocal_get, beq_iff_eq, String.reduceEq, if_false, if_true, hs, hp] <;> rfl

end Benchmarks.UniswapV4PoolManager
