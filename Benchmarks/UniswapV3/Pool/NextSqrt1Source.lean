import Benchmarks.UniswapV3.Pool.NextSqrt1OutputSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt1Returns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hfit : a.Fits) (hv : nextSqrt1Valid a) :
    ExecFuncBody config (nextSqrtFrame imms a) evm (nextSqrtFunction true).body
      (.returned (nextSqrt1OutputFrame imms a) evm
        (some [.int (Int.ofNat (nextSqrt1Result a).toNat)])) := by
  have hb : ExecBlock config (nextSqrtFrame imms a) evm (nextSqrt1Branch a.add)
      (.returned (nextSqrt1OutputFrame imms a) evm
        (some [.int (Int.ofNat (nextSqrt1Result a).toNat)])) := by
    rw [← List.take_append_drop 3 (nextSqrt1Branch a.add)]
    exact execBlock_append_ok (nextSqrt1QuotientSource imms evm a hv.1)
      (nextSqrt1OutputReturns imms evm a hfit hv.2)
  have he := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrtGet imms a).2.2.2
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  cases ha : a.add
  · exact ExecStmt.iteFalse (by simpa only [ha] using he) (by simpa only [ha] using hb)
  · exact ExecStmt.iteTrue (by simpa only [ha] using he) (by simpa only [ha] using hb)

theorem nextSqrt1Reverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬nextSqrt1Valid a) :
    ExecFuncBody config (nextSqrtFrame imms a) evm (nextSqrtFunction true).body .reverted := by
  have hb : ExecBlock config (nextSqrtFrame imms a) evm (nextSqrt1Branch a.add) .reverted := by
    rw [← List.take_append_drop 3 (nextSqrt1Branch a.add)]
    by_cases hq : nextSqrt1QuotientValid a
    · exact execBlock_append_ok (nextSqrt1QuotientSource imms evm a hq)
        (nextSqrt1OutputReverts imms evm a (fun ho ↦ hv ⟨hq, ho⟩))
    · exact execBlock_reverted_append (nextSqrt1QuotientReverts imms evm a hq)
  have he := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrtGet imms a).2.2.2
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  cases ha : a.add
  · exact ExecStmt.iteFalse (by simpa only [ha] using he) (by simpa only [ha] using hb)
  · exact ExecStmt.iteTrue (by simpa only [ha] using he) (by simpa only [ha] using hb)

end Benchmarks.UniswapV3.Pool
