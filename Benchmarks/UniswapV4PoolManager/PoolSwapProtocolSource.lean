import Benchmarks.UniswapV4PoolManager.PoolSwapFeeWords
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax
import Benchmarks.UniswapV4PoolManager.WordConditionalSource
import Benchmarks.UniswapV4PoolManager.WordBorrowSource
import Benchmarks.UniswapV4PoolManager.WordBoolean
import Benchmarks.UniswapV4PoolManager.WordWrappingSource
import Benchmarks.UniswapV4PoolManager.PoolCheckSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapProtocolFrame (f : Frame) (s : PoolSwapStepWords) (fee protocol amount : UInt256) : Frame :=
  if protocol = ⟨0⟩ then f
  else wordLocal
    (valueLocal (wordLocal f "delta" (poolSwapProtocolShare s fee protocol))
      "step" (poolSwapStepValue (poolSwapProtocolStep s fee protocol)))
    "amountToProtocol" (poolSwapProtocolAmount s fee protocol amount)

theorem poolSwapProtocolSource {f : Frame} {evm : State}
    {s : PoolSwapStepWords} {fee protocol amount : UInt256}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hf : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hp : f.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat)))
    (ha : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat))) :
    ExecStmt config f evm poolSwapLoopBody[16]! (.ok (poolSwapProtocolFrame f s fee protocol amount) evm) := by
  have hg : evalExpr? config f evm (.binary .gt (.var "protocolFee") (.intLit 0)) =
      .ok (.bool (decide (protocol ≠ ⟨0⟩))) := by
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordPositive_iff] using evalWordGt (evalLocalValue hp)
      (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
  by_cases hz : protocol = ⟨0⟩
  · rw [poolSwapProtocolFrame, if_pos hz]
    exact ExecStmt.iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hg) ExecBlock.nil
  · rw [poolSwapProtocolFrame, if_neg hz]
    let delta := poolSwapProtocolShare s fee protocol
    let f1 := wordLocal f "delta" delta
    let f2 := valueLocal f1 "step" (poolSwapStepValue (poolSwapProtocolStep s fee protocol))
    have hdelta := evalWordConditional (evalEqWords (evalLocalValue (cfg := config) (evm := evm) hf) (evalLocalValue hp))
      (evalStructField (field := "feeAmount") (evalLocalValue hs) rfl)
      (evalWordDiv (evalWordMul
        (evalWordAdd (evalStructField (field := "amountIn") (evalLocalValue hs) rfl)
          (evalStructField (field := "feeAmount") (evalLocalValue hs) rfl)) (evalLocalValue hp))
        (show evalExpr? config f evm (.intLit 1000000) = .ok (.int (Int.ofNat (UInt256.ofNat 1000000).toNat)) by
          simp only [evalExpr?, pure]; rfl) (by decide))
    have hs1 : f1.locals.get? "step" = some (poolSwapStepValue s) :=
      (store_get_ne _ _ (by decide : ("delta" == "step") = false)).trans hs
    have hfee : ExecStmt config f1 evm
        (.assign .localVar {base := "step", steps := [.field "feeAmount"]}
          (.cast (.binary .sub (.field (.var "step") "feeAmount") (.var "delta")) (.elem (.int (.uint ⟨256, by decide⟩)))))
        (.ok f2 evm) := by
      simpa only [f2, poolSwapProtocolStep, if_neg hz] using
        ExecStmt.assign (evalWordSub (evalStructField (field := "feeAmount") (evalLocalValue hs1) rfl)
          (evalLocalValue (store_get_self _ _ _))) (assignLocalField hs1 rfl rfl)
    have ha2 : f2.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat)) :=
      (store_get_ne2 _ _ _ (by decide : ("delta" == "amountToProtocol") = false)
        (by decide : ("step" == "amountToProtocol") = false)).trans ha
    have hd2 : f2.locals.get? "delta" = some (.int (Int.ofNat delta.toNat)) :=
      (store_get_ne _ _ (by decide : ("step" == "delta") = false)).trans (store_get_self _ _ _)
    have hamount : ExecStmt config f2 evm
        (.assign .localVar {base := "amountToProtocol"}
          (.cast (.binary .add (.var "amountToProtocol") (.var "delta")) (.elem (.int (.uint ⟨256, by decide⟩)))))
        (.ok (wordLocal f2 "amountToProtocol" (poolSwapProtocolAmount s fee protocol amount)) evm) := by
      simpa only [poolSwapProtocolAmount, if_neg hz] using
        ExecStmt.assign (evalWordAdd (evalLocalValue ha2) (evalLocalValue hd2)) (assignLocalValue ha2)
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hg)
      (ExecBlock.consNormal (ExecStmt.letDecl hdelta) (ExecBlock.consNormal hfee (execBlock_singleton hamount)))

end Benchmarks.UniswapV4PoolManager
