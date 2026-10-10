import Benchmarks.UniswapV4PoolManager.PoolModifyTickFrames
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyTwoTicksResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  let packed := tickFieldWord evm id (EVM.signed p.lower) .liquidityPacked
  continueBlockResult (fun f1 post => poolModifyTickResult f1 post id (EVM.signed p.upper) p.delta true
    (tickFlipped packed p.delta) (EVM.wordOfInt (tickGrossAfterInt packed p.delta)) false ⟨0⟩)
    (poolModifyTickResult f evm id (EVM.signed p.lower) p.delta false false ⟨0⟩ false ⟨0⟩)

def poolModifyLowerPacked (evm : State) (id : UInt256) (p : PoolModifyParams) : UInt256 :=
  tickFieldWord evm id (EVM.signed p.lower) .liquidityPacked
def poolModifyUpperPacked (evm : State) (id : UInt256) (p : PoolModifyParams) : UInt256 :=
  tickFieldWord (poolUpdateTickPost evm id (EVM.signed p.lower) p.delta false) id
    (EVM.signed p.upper) .liquidityPacked
def poolModifyTwoTicksFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : Frame :=
  let f1 := poolModifyTickAfterFrame f evm id (EVM.signed p.lower) p.delta false false ⟨0⟩ false ⟨0⟩
  poolModifyTickAfterFrame f1 (poolUpdateTickPost evm id (EVM.signed p.lower) p.delta false)
    id (EVM.signed p.upper) p.delta true
    (tickFlipped (poolModifyLowerPacked evm id p) p.delta)
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta)) false ⟨0⟩
def poolModifyTwoTicksState (evm : State) (id : UInt256) (p : PoolModifyParams) : Value :=
  poolModifyStateValue
    (tickFlipped (poolModifyLowerPacked evm id p) p.delta)
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
    (tickFlipped (poolModifyUpperPacked evm id p) p.delta)
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta))

theorem poolModifyTwoTicksResult_normal {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyTwoTicksResult f evm id p = .ok f' post) :
    f' = poolModifyTwoTicksFrame f evm id p ∧
    post = poolUpdateTickPost (poolUpdateTickPost evm id (EVM.signed p.lower) p.delta false)
      id (EVM.signed p.upper) p.delta true := by
  obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
  obtain ⟨rfl, rfl⟩ := poolModifyTickResult_normal hlo
  exact poolModifyTickResult_normal hup

theorem poolModifyTwoTicksResult_context {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (h : poolModifyTwoTicksResult f evm id p = .ok f' post) :
    PoolModifyContext f' id p := by
  rw [(poolModifyTwoTicksResult_normal h).1]
  exact poolModifyTickAfterFrame_context
    (poolModifyTickAfterFrame_context hc _ _ _ _ _ _ _ _) _ _ _ _ _ _ _ _

theorem poolModifyTwoTicksResult_state {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyTwoTicksResult f evm id p = .ok f' post) :
    f'.locals.get? "state" = some (poolModifyTwoTicksState evm id p) := by
  rw [(poolModifyTwoTicksResult_normal h).1]
  exact store_get_self _ _ _

theorem poolModifyTwoTicks {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hl : f.locals.get? "tickLower" = some (.int (EVM.signed p.lower)))
    (hu : f.locals.get? "tickUpper" = some (.int (EVM.signed p.upper)))
    (hd : f.locals.get? "liquidityDelta" = some (.int p.delta))
    (hstate : f.locals.get? "state" = some (poolModifyStateValue false ⟨0⟩ false ⟨0⟩)) :
    ExecBlock config f evm (poolModifyTickBlock false ++ poolModifyTickBlock true)
      (poolModifyTwoTicksResult f evm id p) := by
  have hlo := poolModifyTick (upper := false) (f := f) (evm := evm) hf hs hl hd hstate
  apply execBlock_continue hlo
  intro f1 post hpost
  obtain ⟨values, rfl⟩ := poolModifyTickResult_frame hpost
  apply poolModifyTick (upper := true)
  · dsimp only [poolModifyTickFrame, resumeAfterInternalCall, poolModifyTickAliasFrame]
    exact hf
  · rw [poolModifyTickFrame_get _ _ _ _ _ _ _ _ _ (by decide)]
    exact (store_get_ne2 _ _ _ (by decide : (poolModifyTickAlias false == "self") = false)
      (by decide : ("__c1" == "self") = false)).trans hs
  · rw [poolModifyTickFrame_get _ _ _ _ _ _ _ _ _ (by decide)]
    exact (store_get_ne2 _ _ _ (by decide : (poolModifyTickAlias false == "tickUpper") = false)
      (by decide : ("__c1" == "tickUpper") = false)).trans hu
  · rw [poolModifyTickFrame_get _ _ _ _ _ _ _ _ _ (by decide)]
    exact (store_get_ne2 _ _ _ (by decide : (poolModifyTickAlias false == "liquidityDelta") = false)
      (by decide : ("__c1" == "liquidityDelta") = false)).trans hd
  · exact store_get_self _ _ _

end Benchmarks.UniswapV4PoolManager
