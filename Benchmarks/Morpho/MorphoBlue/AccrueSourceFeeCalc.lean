import Benchmarks.Morpho.MorphoBlue.AccrueSourceFee
import Benchmarks.Morpho.MorphoBlue.AccrueFeeMath

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueFeeCalcLocals (locals : Store) (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : Store :=
  let l1 := locals.insert "feeAmount" (.int (Int.ofNat (accrueFeeAmount σ I id interest).toNat))
  let l2 := l1.insert "__c6" (.int (Int.ofNat (accrueFeeShares σ I id interest).toNat))
  l2.insert "feeShares" (.int (Int.ofNat (accrueFeeShares σ I id interest).toNat))

theorem morphoAccrueFeeCalcSource (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (interest : UInt256) (oldShares : Value) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "interest") = .ok (.int (Int.ofNat interest.toNat)))
    (hg : locals.get? "feeShares" = some oldShares)
    (hfit : AccrueFeeFits evm.accountMap evm.executionEnv p.id interest) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms } accrueFeeBody
      { contract := contract, locals := accrueFeeCalcLocals locals evm.accountMap evm.executionEnv p.id interest,
        immutables := imms } (accrueFeeBody.drop 3) := by
  let fee := accrueFeeAmount evm.accountMap evm.executionEnv p.id interest
  let shares := accrueFeeShares evm.accountMap evm.executionEnv p.id interest
  let l1 := locals.insert "feeAmount" (.int (Int.ofNat fee.toNat))
  let l2 := l1.insert "__c6" (.int (Int.ofNat shares.toNat))
  have h1 : ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[0]!
      (.ok { contract := contract, locals := l1, immutables := imms } evm) :=
    morphoAccrueFeeAmountStep p locals imms evm interest hl he hfit.1
  have hl1 : MarketLocals p l1 := hl.insert "feeAmount" _ (by decide)
  have he1 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
      (.var "feeAmount") = .ok (.int (Int.ofNat fee.toNat)) := by
    simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have h2 : ExecStmt config { contract := contract, locals := l1, immutables := imms } evm accrueFeeBody[1]!
      (.ok { contract := contract, locals := l2, immutables := imms } evm) :=
    morphoAccrueFeeSharesStep p l1 imms evm fee hl1 he1 hfit.2.1 hfit.2.2
  have he2 : evalExpr? config { contract := contract, locals := l2, immutables := imms } evm
      (.var "__c6") = .ok (.int (Int.ofNat shares.toNat)) := by
    simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have hg2 : l2.get? "feeShares" = some oldShares := by
    simp only [l2, l1, store_get_ne (k := "__c6") (a := "feeShares") _ _ (by decide),
      store_get_ne (k := "feeAmount") (a := "feeShares") _ _ (by decide), hg]
  have h3 := morphoAccrueFeeAssignLocal l2 imms evm shares oldShares hg2 he2
  exact ⟨fun hr => ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consNormal h3 hr))⟩

theorem morphoAccrueFeeCalcSourceReverts (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (interest : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "interest") = .ok (.int (Int.ofNat interest.toNat)))
    (hbad : ¬ AccrueFeeFits evm.accountMap evm.executionEnv p.id interest) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody .reverted := by
  by_cases hm : interest.toNat * (marketFieldWord evm.accountMap evm.executionEnv p.id 5).toNat < UInt256.size
  · let fee := accrueFeeAmount evm.accountMap evm.executionEnv p.id interest
    let l1 := locals.insert "feeAmount" (.int (Int.ofNat fee.toNat))
    apply ExecBlock.consNormal (morphoAccrueFeeAmountStep p locals imms evm interest hl he hm)
    apply ExecBlock.consRevert
    have hl1 : MarketLocals p l1 := hl.insert "feeAmount" _ (by decide)
    have he1 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
        (.var "feeAmount") = .ok (.int (Int.ofNat fee.toNat)) := by
      simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
    by_cases hs : fee.toNat ≤ (marketFieldWord evm.accountMap evm.executionEnv p.id 0).toNat
    · exact morphoAccrueFeeSharesReverts p l1 imms evm fee hl1 he1 hs (fun hf => hbad ⟨hm, hs, hf⟩)
    · exact morphoAccrueFeeSharesUnderflow p l1 imms evm fee hl1 he1 (Nat.lt_of_not_ge hs)
  · exact ExecBlock.consRevert (morphoAccrueFeeAmountReverts p locals imms evm interest hl he (Nat.le_of_not_gt hm))

theorem accrueFeeCalcLocals_market (p : MarketParamsWords) (locals : Store) (σ : AccountMap)
    (I : ExecutionEnv) (interest : UInt256) (hl : MarketLocals p locals) :
    MarketLocals p (accrueFeeCalcLocals locals σ I p.id interest) :=
  ((hl.insert "feeAmount" _ (by decide)).insert "__c6" _ (by decide)).insert "feeShares" _ (by decide)

theorem accrueFeeCalcLocals_eval (p : MarketParamsWords) (locals imms : Store) (σ : AccountMap)
    (I : ExecutionEnv) (interest : UInt256) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := accrueFeeCalcLocals locals σ I p.id interest, immutables := imms }
      evm (.var "feeShares") = .ok (.int (Int.ofNat (accrueFeeShares σ I p.id interest).toNat)) := by
  simp only [evalExpr?, accrueFeeCalcLocals, store_get_self, EvalResult.ofOption]

end Benchmarks.Morpho.MorphoBlue
