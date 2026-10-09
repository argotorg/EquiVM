import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem constructorSourceField {c : ConstructorConfig} {frame : Frame} {evm : EVM.State}
    {name : Ident} {value : Value}
    (hlocal : frame.locals.get? "config" = some (constructorConfigValue c))
    (hfield : lookupField? (constructorConfigValue c) name = some value) :
    evalExpr? config frame evm (.field (.var "config") name) = .ok value := by
  simp only [evalExpr?, hlocal, EvalResult.ofOption, bind, EvalResult.bind]
  change EvalResult.ofOption .typeError (lookupField? (constructorConfigValue c) name) = _
  rw [hfield]
  rfl

def constructorInitialImms (c : ConstructorConfig) (w : UInt256) : Store :=
  let imms := (initialImmutables contract).insert "governor" (.address c.governor)
  let imms := imms.insert "pauseGuardian" (.address c.pauseGuardian)
  let imms := imms.insert "baseToken" (.address c.baseToken)
  let imms := imms.insert "baseTokenPriceFeed" (.address c.baseTokenPriceFeed)
  let imms := imms.insert "extensionDelegate" (.address c.extensionDelegate)
  let imms := imms.insert "storeFrontPriceFactor" (.int (Int.ofNat c.storeFrontPriceFactor.val))
  imms.insert "decimals" (.int (Int.ofNat w.toNat))

def constructorSourceInitialImms (c : ConstructorConfig) (w feed : UInt256) : Frame :=
  { constructorSourcePriceFeed c w feed with immutables := constructorInitialImms c w }

theorem constructorSourceInitialImms_exec {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' : EVM.State} (hw : w.toNat ≤ 18)
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 9)
      (.ok (constructorSourcePriceFeed c w feed) evm')) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 16)
      (.ok (constructorSourceInitialImms c w feed) evm') := by
  change ExecBlock config _ _ (contract.ctor.body.take 9 ++
    [.setImmutable "governor" (.field (.var "config") "governor"),
      .setImmutable "pauseGuardian" (.field (.var "config") "pauseGuardian"),
      .setImmutable "baseToken" (.field (.var "config") "baseToken"),
      .setImmutable "baseTokenPriceFeed" (.field (.var "config") "baseTokenPriceFeed"),
      .setImmutable "extensionDelegate" (.field (.var "config") "extensionDelegate"),
      .setImmutable "storeFrontPriceFactor" (.field (.var "config") "storeFrontPriceFactor"),
      .setImmutable "decimals" (.var "decimals_")]) _
  apply execBlockAppendOk hp
  have hl : (constructorSourcePriceFeed c w feed).locals.get? "config" =
      some (constructorConfigValue c) := by
    simp only [constructorSourcePriceFeed, constructorSourceDecimals, constructorSourceConfig,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .address c.governor)
    (ty := .address) ?_ rfl rfl) ?_
  · exact constructorSourceField hl rfl
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .address c.pauseGuardian)
    (ty := .address) ?_ rfl rfl) ?_
  · exact constructorSourceField hl rfl
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .address c.baseToken)
    (ty := .address) ?_ rfl rfl) ?_
  · exact constructorSourceField hl rfl
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .address c.baseTokenPriceFeed)
    (ty := .address) ?_ rfl rfl) ?_
  · exact constructorSourceField hl rfl
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .address c.extensionDelegate)
    (ty := .address) ?_ rfl rfl) ?_
  · exact constructorSourceField hl rfl
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat c.storeFrontPriceFactor.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (by
      have hb := c.storeFrontPriceFactor.isLt
      simp [elemValueFits]
      omega)) ?_
  · exact constructorSourceField hl rfl
  apply ExecBlock.consNormal (ExecStmt.setImmutable (value := .int (Int.ofNat w.toNat))
    (ty := .int (.uint ⟨8, by decide⟩)) (by
      simp only [evalExpr?, constructorSourcePriceFeed, constructorSourceDecimals,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl) rfl (by simp [elemValueFits]; omega))
  exact .nil

end Benchmarks.CompoundIII.Comet
