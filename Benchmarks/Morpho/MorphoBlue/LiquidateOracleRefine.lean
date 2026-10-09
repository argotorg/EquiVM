import Benchmarks.Morpho.MorphoBlue.LiquidateCallPrepare
import Benchmarks.Morpho.MorphoBlue.LiquidateAccrueRefine
import Benchmarks.Morpho.MorphoBlue.OraclePriceSource
import Benchmarks.Morpho.MorphoBlue.HealthyPriceRefine
import Benchmarks.Morpho.MorphoBlue.HeapWordWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateOracleRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account seized shares srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 10) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateOracleRefines v ee g s0 p account seized shares srcOff len data locals imms evm mem fp R
  | ok {locals' evm' σ' mem' fp' aw' out' k' C'} (price : UInt256) (z : Bool) :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateTransition.body.drop 10) { contract := contract, locals := locals', immutables := imms }
        evm' (liquidateTransition.body.drop 13) → LiquidateLocals p account seized shares data locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 320))) →
      locals'.get? "collateralPrice" = some (.int (Int.ofNat price.toNat)) →
      locals'.get? "__c4" = some (.bool z) → SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 896 →
      HeapAdvance mem fp mem' fp' 32 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1577)
        ([if z then UInt256.ofNat 1 else UInt256.ofNat 0, UInt256.ofNat 1638, price] ++
          liquidateGuardTail p.id seized shares srcOff len R) mem' aw' out' σ' k' C' →
      LiquidateOracleRefines v ee g s0 p account seized shares srcOff len data locals imms evm mem fp R

theorem morphoLiquidateOracleRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw fp account seized shares srcOff len : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 48 ≤ 1024) (hc : p.Canonical) (ha : account.toNat < EVM.addressModulus)
    (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateLocals p account seized shares data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 928)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 352))))
    (hparams : p.InMemory (UInt256.ofNat 128) mem) (hsize : 288 ≤ mem.size) (hbefore : 288 ≤ fp.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1470)
      (liquidateGuardTail p.id seized shares srcOff len R) mem aw out σ k C) :
    LiquidateOracleRefines v ee g s0 p account seized shares srcOff len data locals imms evm mem fp R := by
  let l1 := locals.insert "oracle" (.address (AccountAddress.ofNat p.oracle.toNat))
  have hl1 : LiquidateLocals p account seized shares data l1 := hl.insert _ _ (by decide) (by decide)
  have helet : ExecStmt config { contract := contract, locals := locals, immutables := imms }
      evm liquidateTransition.body[10]!
      (.ok { contract := contract, locals := l1, immutables := imms } evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?,
      EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 10) { contract := contract, locals := l1, immutables := imms }
      evm (liquidateTransition.body.drop 11) := StateBlock.start.step helet
  have hetarget : evalExpr? config { contract := contract, locals := l1, immutables := imms }
      evm (.var "oracle") = .ok (.address (AccountAddress.ofNat p.oracle.toNat)) := by
    simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  obtain ⟨gasArg, a1, k1, C1, rd1⟩ := morphoLiquidatePrepareCall (v := v) p (by omega) hc.2.2.1 hm.free
    (by simpa only [show UInt256.ofNat 128 + UInt256.ofNat (32 * 2) = UInt256.ofNat 192 from by decide]
      using hparams ⟨2, by decide⟩) h
  obtain ⟨hm1, hp1⟩ := hm.writeAbove fp.toNat oraclePriceSelectorWord (le_refl _) (by omega)
  have hgap : fp.toNat - mem.size < USize.size := by have hh := hm.gap; omega
  have hin : fp.toNat + 32 ≤ (writeWord mem fp.toNat oraclePriceSelectorWord).size := by
    rw [writeWord_size _ _ _ hgap]; omega
  obtain ⟨evm', z, out', hcall, hs', hout, hrd⟩ := morphoLiquidateCall (v := v) p hs (by omega)
    (by have hh := hm.space; omega) hm.lower hin (oraclePriceCallMem_read _ _ hgap) rd1
  by_cases hok : z = true ∧ 32 ≤ out'.size
  swap
  · rw [if_neg hok] at hrd
    exact .reverted (ab1.reverts (oraclePriceSourceReverts "collateralPrice" z out' hetarget hcall hok)) hrd
  rw [if_pos hok, haccount] at hrd
  obtain ⟨a2, k2, C2, rd2⟩ := hrd
  rcases hok with ⟨rfl, hlen⟩
  have hecall := oraclePriceSourceOk "collateralPrice" out' hetarget hcall hlen hout
  let price := calldataWord out' 0
  let l2 := l1.insert "collateralPrice" (.int (Int.ofNat price.toNat))
  have hl2 : LiquidateLocals p account seized shares data l2 := hl1.insert _ _ (by decide) (by decide)
  have heprice : evalExpr? config { contract := contract, locals := l2, immutables := imms }
      evm' (.var "collateralPrice") = .ok (.int (Int.ofNat price.toNat)) := by
    simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have heargs : evalExprs? config { contract := contract, locals := l2, immutables := imms } evm'
      [.var "marketParams", .var "id", .var "borrower", .var "collateralPrice"] =
      .ok [p.value, .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id),
        .address (AccountAddress.ofNat account.toNat), .int (Int.ofNat price.toNat)] := by
    simp only [evalExprs?, hl2.evalParams imms evm', hl2.evalId imms evm', hl2.evalBorrower imms evm',
      heprice, pure, bind, EvalResult.bind]
  have hab := ab1.step hecall
  have houtWord : out'.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hm2 := hm1.callReturn out' houtWord hin (by decide)
  have had2 := hm1.callReturnAdvance out' houtWord hin
  have hp2 := hp1.trans had2.preserves
  have hparams2 := hparams.ofPrefix hp2 (by decide) (by decide) hsize hbefore
  have href := morphoHealthyPriceRefine (v := v) p imms (by change R.length + 9 + 32 ≤ 1024; omega)
    ha hs' hparams2 (le_trans hsize hp2.size) (by rw [morphoPatchedValidJumps v]; jump_dest) rd2
  cases href with
  | reverted he hr =>
    exact .reverted (hab.reverts (internalCallFunctionRevert (callee := healthyPriceFunction) heargs rfl rfl he)) hr
  | @ok frame' σ' a3 out3 k3 C3 z' he hs'' rd3 =>
    have hehealthy := internalCallFunctionReturn (callee := healthyPriceFunction) (name := "_isHealthyWithPrice")
      (retVar := "__c4") heargs rfl rfl he
    refine .ok price z' (hab.step hehealthy) (hl2.insert _ _ (by decide) (by decide)) ?_
      (by rw [store_get_ne _ _ (by decide)]; exact store_get_self _ _ _) (store_get_self _ _ _) hs''
      (hm2.healthyPrice p.id account) ?_ rd3
    · simp only [store_get_ne _ _ (show ("__c4" == "__memory") = false by decide), l2, l1,
        store_get_ne _ _ (show ("collateralPrice" == "__memory") = false by decide),
        store_get_ne _ _ (show ("oracle" == "__memory") = false by decide), hget, had2.cursor]
    · exact ⟨hp2.trans (healthyPriceMem_prefix p.id account _ fp.toNat), had2.cursor⟩

end Benchmarks.Morpho.MorphoBlue
