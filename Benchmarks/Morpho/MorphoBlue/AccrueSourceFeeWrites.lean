import Benchmarks.Morpho.MorphoBlue.AccrueSourceFeeCalc

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueFeePositionState (evm : EVM.State) (id shares : UInt256) : EVM.State :=
  storePositionSupplyShares evm id (accrueFeeRecipient evm.accountMap evm.executionEnv)
    (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv id) evm.accountMap evm.executionEnv + shares)

def accrueFeeSharesState (evm : EVM.State) (id shares : UInt256) : EVM.State :=
  let e1 := accrueFeePositionState evm id shares
  storeMarketField e1 id ⟨1, by decide⟩ (marketFieldWord e1.accountMap e1.executionEnv id 1 + shares)

def AccrueFeeWritesFit (evm : EVM.State) (id shares : UInt256) : Prop :=
  (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv id) evm.accountMap evm.executionEnv).toNat +
    shares.toNat < UInt256.size ∧
  shares.toNat < 2 ^ 128 ∧
  (marketFieldWord (accrueFeePositionState evm id shares).accountMap
    (accrueFeePositionState evm id shares).executionEnv id 1).toNat + shares.toNat < 2 ^ 128

theorem morphoAccrueFeeWritesSourceOk (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (shares : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat)))
    (hf : AccrueFeeWritesFit evm p.id shares) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm (accrueFeeBody.drop 3)
      (.ok { contract := contract, locals := locals.insert "__c7" (.int (Int.ofNat shares.toNat)), immutables := imms }
        (accrueFeeSharesState evm p.id shares)) := by
  let e1 := accrueFeePositionState evm p.id shares
  have hs := morphoAccrueFeePositionAssign p locals imms evm shares hl he hf.1
  have he1 : evalExpr? config { contract := contract, locals := locals, immutables := imms } e1
      (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat)) := by simpa only [evalExpr?] using he
  have hn := morphoToUint128CallOk shares e1 locals imms (.var "feeShares") "__c7" he1 hf.2.1
  have hl1 := hl.insert "__c7" (.int (Int.ofNat shares.toNat)) (by decide)
  have he2 : evalExpr? config { contract := contract, locals := locals.insert "__c7" (.int (Int.ofNat shares.toNat)), immutables := imms } e1
      (.var "__c7") = .ok (.int (Int.ofNat shares.toNat)) := by
    simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  have hu := morphoAccrueAssetsAssign p _ imms e1 ⟨1, by decide⟩ "__c7" shares hl1 he2 hf.2.2
  exact ExecBlock.consNormal hs (ExecBlock.consNormal hn (ExecBlock.consNormal hu ExecBlock.nil))

theorem morphoAccrueFeeWritesSourceReverts (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (shares : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat)))
    (hbad : ¬ AccrueFeeWritesFit evm p.id shares) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (accrueFeeBody.drop 3) .reverted := by
  by_cases hp : (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv p.id)
      evm.accountMap evm.executionEnv).toNat + shares.toNat < UInt256.size
  · let e1 := accrueFeePositionState evm p.id shares
    apply ExecBlock.consNormal (morphoAccrueFeePositionAssign p locals imms evm shares hl he hp)
    have he1 : evalExpr? config { contract := contract, locals := locals, immutables := imms } e1
        (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat)) := by simpa only [evalExpr?] using he
    by_cases hc : shares.toNat < 2 ^ 128
    · apply ExecBlock.consNormal (morphoToUint128CallOk shares e1 locals imms (.var "feeShares") "__c7" he1 hc)
      have hl1 := hl.insert "__c7" (.int (Int.ofNat shares.toNat)) (by decide)
      have he2 : evalExpr? config { contract := contract, locals := locals.insert "__c7" (.int (Int.ofNat shares.toNat)), immutables := imms } e1
          (.var "__c7") = .ok (.int (Int.ofNat shares.toNat)) := by
        simp only [evalExpr?, store_get_self, EvalResult.ofOption]
      exact ExecBlock.consRevert (morphoAccrueAssetsAssignReverts p _ imms e1 ⟨1, by decide⟩ "__c7" shares
        hl1 he2 (Nat.le_of_not_gt (fun hs => hbad ⟨hp, hc, hs⟩)))
    · exact ExecBlock.consRevert (morphoToUint128CallReverts shares e1 locals imms (.var "feeShares") "__c7" he1
        (Nat.le_of_not_gt hc))
  · exact ExecBlock.consRevert (morphoAccrueFeePositionReverts p locals imms evm shares hl he (Nat.le_of_not_gt hp))

end Benchmarks.Morpho.MorphoBlue
