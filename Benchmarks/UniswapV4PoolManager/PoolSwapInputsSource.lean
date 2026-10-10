import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax
import Benchmarks.UniswapV4PoolManager.PoolStorage
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapZeroResult : PoolSwapResultWords := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

def poolSwapInputsFrame (f : Frame) (packed : UInt256) (zeroForOne : Bool) : Frame :=
  let f1 := valueLocal f "swapDelta" (.int 0)
  let f2 := wordLocal f1 "amountToProtocol" ⟨0⟩
  let f3 := wordLocal f2 "swapFee" ⟨0⟩
  let f4 := valueLocal f3 "result" (poolSwapResultValue poolSwapZeroResult)
  let f5 := valueLocal f4 "slot0Start" (wordBytes32Value packed)
  valueLocal f5 "zeroForOne" (.bool zeroForOne)

theorem poolSwapInputsFrame_contract (f : Frame) (packed : UInt256) (zeroForOne : Bool) :
    (poolSwapInputsFrame f packed zeroForOne).contract = f.contract := by
  simp only [poolSwapInputsFrame, valueLocal_contract, wordLocal_contract]

theorem poolSwapInputsFrame_get (f : Frame) (packed : UInt256) (zeroForOne : Bool) (key : Ident)
    (hd : ("swapDelta" == key) = false) (ha : ("amountToProtocol" == key) = false)
    (hf : ("swapFee" == key) = false) (hr : ("result" == key) = false)
    (hs : ("slot0Start" == key) = false) (hz : ("zeroForOne" == key) = false) :
    (poolSwapInputsFrame f packed zeroForOne).locals.get? key = f.locals.get? key := by
  simp only [poolSwapInputsFrame, valueLocal_get, wordLocal_get, hd, ha, hf, hr, hs, hz,
    Bool.false_eq_true, if_false]

theorem poolSwapInputsSource {f : Frame} {evm : State} {id : UInt256} {p : PoolSwapParamsWords}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) :
    ExecBlock config f evm (poolSwapFunction.body.take 6)
      (.ok (poolSwapInputsFrame f (poolSlot0Word evm id) p.zeroForOne) evm) := by
  let f1 := valueLocal f "swapDelta" (.int 0)
  let f2 := wordLocal f1 "amountToProtocol" ⟨0⟩
  let f3 := wordLocal f2 "swapFee" ⟨0⟩
  let f4 := valueLocal f3 "result" (poolSwapResultValue poolSwapZeroResult)
  let f5 := valueLocal f4 "slot0Start" (wordBytes32Value (poolSlot0Word evm id))
  have h0 : ExecStmt config f evm poolSwapFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have h1 : ExecStmt config f1 evm poolSwapFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h2 : ExecStmt config f2 evm poolSwapFunction.body[2]! (.ok f3 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h3 : ExecStmt config f3 evm poolSwapFunction.body[3]! (.ok f4 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, evalStructFields?, pure, bind, EvalResult.bind]; rfl)
  have hs4 : f4.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("swapDelta" == "self") = false)
      (by decide : ("amountToProtocol" == "self") = false) (by decide : ("swapFee" == "self") = false)
      (by decide : ("result" == "self") = false)).trans hs
  have h4 : ExecStmt config f4 evm poolSwapFunction.body[4]! (.ok f5 evm) :=
    ExecStmt.letDecl (poolSlot0_read hs4)
  have hp5 : f5.locals.get? "params" = some (poolSwapParamsValue p) :=
    (store_get_ne _ _ (by decide : ("slot0Start" == "params") = false)).trans
      ((store_get_ne4 _ _ _ _ _ (by decide : ("swapDelta" == "params") = false)
        (by decide : ("amountToProtocol" == "params") = false) (by decide : ("swapFee" == "params") = false)
        (by decide : ("result" == "params") = false)).trans hp)
  have h5 : ExecStmt config f5 evm poolSwapFunction.body[5]!
      (.ok (poolSwapInputsFrame f (poolSlot0Word evm id) p.zeroForOne) evm) :=
    ExecStmt.letDecl (evalStructField (field := "zeroForOne") (evalLocalValue hp5) rfl)
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (ExecBlock.consNormal h4 (execBlock_singleton h5)))))

end Benchmarks.UniswapV4PoolManager
