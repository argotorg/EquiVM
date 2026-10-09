import Benchmarks.Morpho.MorphoBlue.HealthyLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev healthyPriceFunction : FunctionDecl := contract.functions[10]!

def healthyPriceBorrowFrame (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State) : Frame :=
  { healthyPriceFrame p account price imms with locals :=
    ((healthyPriceFrame p account price imms).locals.insert "borrowed"
      (.int (Int.ofNat (healthyBorrowed evm.accountMap evm.executionEnv p account).toNat))) }

def healthyPriceValueFrame (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State) : Frame :=
  { healthyPriceBorrowFrame p account price imms evm with locals :=
    ((healthyPriceBorrowFrame p account price imms evm).locals.insert "collateralValue"
      (.int (Int.ofNat (healthyCollateralValue evm.accountMap evm.executionEnv p account price).toNat))) }

def healthyPriceResultFrame (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State) : Frame :=
  { healthyPriceValueFrame p account price imms evm with locals :=
    ((healthyPriceValueFrame p account price imms evm).locals.insert "maxBorrow"
      (.int (Int.ofNat (healthyMaxBorrow evm.accountMap evm.executionEnv p account price).toNat))) }

instance (σ ee p account price) : Decidable (HealthyPriceFits σ ee p account price) := by
  unfold HealthyPriceFits AssetsUpFits MulDivUpFits
  infer_instance

theorem morphoHealthyPriceBody (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus) :
    ExecFuncBody config (healthyPriceFrame p account price imms) evm healthyPriceFunction.body
      (if HealthyPriceFits evm.accountMap evm.executionEnv p account price then
        .returned (healthyPriceResultFrame p account price imms evm) evm
          (some [.bool (healthyPriceResult evm.accountMap evm.executionEnv p account price)])
       else .reverted) := by
  have hl := healthyPriceFrame_locals p account price imms
  have hb := evalCastUint256Word (hl.evalPosition imms evm ⟨1, by decide⟩ hc)
  have ht := hl.evalField imms evm ⟨2, by decide⟩
  have hs := hl.evalField imms evm ⟨3, by decide⟩
  by_cases hf1 : AssetsUpFits (positionFieldWord evm.accountMap evm.executionEnv p.id account 1)
      (marketFieldWord evm.accountMap evm.executionEnv p.id 2) (marketFieldWord evm.accountMap evm.executionEnv p.id 3)
  swap
  · rw [if_neg (fun hh ↦ hf1 hh.1)]
    exact .execBlockRevert (ExecBlock.consRevert (morphoAssetsUpCallReverts _ _ _ evm _ imms _ _ _ _ hb ht hs hf1))
  have hfirst := morphoAssetsUpCallOk _ _ _ evm _ imms _ _ _ "borrowed" hb ht hs hf1
  have ab1 : ABlock config evm (healthyPriceFrame p account price imms) healthyPriceFunction.body
      (healthyPriceBorrowFrame p account price imms evm) (healthyPriceFunction.body.drop 1) :=
    ⟨fun h ↦ ExecBlock.consNormal hfirst h⟩
  have hl1 := hl.insert "borrowed" (.int (Int.ofNat (healthyBorrowed evm.accountMap evm.executionEnv p account).toNat))
    (by decide) (by decide)
  have hcol := evalCastUint256Word (hl1.evalPosition imms evm ⟨2, by decide⟩ hc)
  have hprice : evalExpr? config (healthyPriceBorrowFrame p account price imms evm) evm
      (.var "collateralPrice") = .ok (.int (Int.ofNat price.toNat)) := by
    simp [evalExpr?, healthyPriceBorrowFrame, healthyPriceFrame, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert, EvalResult.ofOption]
  have hscale : evalExpr? config (healthyPriceBorrowFrame p account price imms evm) evm
      (.intLit 1000000000000000000000000000000000000) = .ok (.int (Int.ofNat oraclePriceScale.toNat)) := by
    simp only [evalExpr?, pure]
    decide +kernel
  by_cases hf2 : (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat * price.toNat < UInt256.size
  swap
  · rw [if_neg (fun hh ↦ hf2 hh.2.1)]
    exact .execBlockRevert (ab1.run (ExecBlock.consRevert (morphoMulDivDownCallReverts _ _ _ evm _ imms _ _ _ _
      hcol hprice hscale (.inl (Nat.le_of_not_gt hf2)))))
  have hsecond := morphoMulDivDownCallOk _ _ _ evm _ imms _ _ _ "collateralValue" hcol hprice hscale hf2 (by decide)
  have ab2 : ABlock config evm (healthyPriceFrame p account price imms) healthyPriceFunction.body
      (healthyPriceValueFrame p account price imms evm) (healthyPriceFunction.body.drop 2) :=
    ⟨fun h ↦ ab1.run (ExecBlock.consNormal hsecond h)⟩
  have hl2 := hl1.insert "collateralValue" (.int (Int.ofNat (healthyCollateralValue evm.accountMap evm.executionEnv p account price).toNat))
    (by decide) (by decide)
  have hvalue : evalExpr? config (healthyPriceValueFrame p account price imms evm) evm
      (.var "collateralValue") = .ok (.int (Int.ofNat (healthyCollateralValue evm.accountMap evm.executionEnv p account price).toNat)) := by
    simp only [evalExpr?, healthyPriceValueFrame, store_get_self, EvalResult.ofOption]
  have hlltv := hl2.evalLltv imms evm
  by_cases hf3 : (healthyCollateralValue evm.accountMap evm.executionEnv p account price).toNat * p.lltv.toNat < UInt256.size
  swap
  · rw [if_neg (fun hh ↦ hf3 hh.2.2)]
    exact .execBlockRevert (ab2.run (ExecBlock.consRevert (morphoWMulDownCallReverts _ _ evm _ imms _ _ _
      hvalue hlltv (Nat.le_of_not_gt hf3))))
  rw [if_pos ⟨hf1, hf2, hf3⟩]
  apply ExecFuncBody.execBlockRet
  apply ab2.run
  apply ExecBlock.consNormal (morphoWMulDownCallOk _ _ evm _ imms _ _ "maxBorrow" hvalue hlltv hf3)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  change evalExpr? config (healthyPriceResultFrame p account price imms evm) evm
    (.binary .ge (.var "maxBorrow") (.var "borrowed")) = _
  simp only [evalExpr?, healthyPriceResultFrame, healthyPriceValueFrame, healthyPriceBorrowFrame,
    store_get_self, store_get_ne (k := "maxBorrow") (a := "borrowed") _ _ (by decide),
    store_get_ne (k := "collateralValue") (a := "borrowed") _ _ (by decide),
    EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_le]
  rfl

theorem morphoHealthyPriceBodyOk (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus) (hf : HealthyPriceFits evm.accountMap evm.executionEnv p account price) :
    ExecFuncBody config (healthyPriceFrame p account price imms) evm healthyPriceFunction.body
      (.returned (healthyPriceResultFrame p account price imms evm) evm
        (some [.bool (healthyPriceResult evm.accountMap evm.executionEnv p account price)])) := by
  simpa only [if_pos hf] using morphoHealthyPriceBody p account price imms evm hc

theorem morphoHealthyPriceBodyReverts (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus) (hf : ¬ HealthyPriceFits evm.accountMap evm.executionEnv p account price) :
    ExecFuncBody config (healthyPriceFrame p account price imms) evm healthyPriceFunction.body .reverted := by
  simpa only [if_neg hf] using morphoHealthyPriceBody p account price imms evm hc


theorem morphoHealthyPriceCallOk (p : MarketParamsWords) (account price : UInt256) (imms locals : Store) (evm : EVM.State)
    (args : List Expr) (retVar : Ident) (hc : account.toNat < EVM.addressModulus)
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok [p.value, .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id),
        .address (AccountAddress.ofNat account.toNat), .int (Int.ofNat price.toNat)])
    (hf : HealthyPriceFits evm.accountMap evm.executionEnv p account price) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_isHealthyWithPrice" args retVar)
      (.ok { contract := contract, locals := (locals.insert retVar
        (.bool (healthyPriceResult evm.accountMap evm.executionEnv p account price))), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := healthyPriceFunction) he rfl rfl
    (morphoHealthyPriceBodyOk p account price imms evm hc hf)

theorem morphoHealthyPriceCallReverts (p : MarketParamsWords) (account price : UInt256) (imms locals : Store) (evm : EVM.State)
    (args : List Expr) (retVar : Ident) (hc : account.toNat < EVM.addressModulus)
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok [p.value, .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id),
        .address (AccountAddress.ofNat account.toNat), .int (Int.ofNat price.toNat)])
    (hf : ¬ HealthyPriceFits evm.accountMap evm.executionEnv p account price) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_isHealthyWithPrice" args retVar) .reverted := by
  exact internalCallFunctionRevert (callee := healthyPriceFunction) he rfl rfl
    (morphoHealthyPriceBodyReverts p account price imms evm hc hf)

end Benchmarks.Morpho.MorphoBlue
