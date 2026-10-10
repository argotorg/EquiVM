import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSetSlot0Body (refName feeName setterName : Ident) : List Stmt :=
  [.letStorage refName {base := "self"},
   .internalCall "Pool_checkPoolInitialized" [.var refName] "__c0",
   .internalCall setterName [.storage {base := "self", steps := [.field "slot0"]}, .var feeName] "__c1",
   .assign .storage {base := "self", steps := [.field "slot0"]} (.var "__c1")]

def poolSetSlot0Frame (f : Frame) (id word : UInt256) (refName : Ident) : Frame :=
  {f with locals := (((f.locals.insert refName (poolRefValue id)).insert "__c0" .unit).insert
    "__c1" (wordBytes32Value word))}

def poolSetSlot0Result (f : Frame) (evm : EVM.State) (id word : UInt256) : ExecResult :=
  if poolSqrtPriceWord evm id = ⟨0⟩ then .reverted else
  if evm.executionEnv.perm = false then .staticViolation else
    .returned f (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolSlot id) word) none

theorem poolSetSlot0BodyExec {f : Frame} {evm : EVM.State} {id fee word : UInt256}
    (refName feeName setterName : Ident)
    (haSelf : (refName == "self") = false) (haFee : (refName == feeName) = false) (hcFee : ("__c0" == feeName) = false)
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (he : f.locals.get? feeName = some (.int (Int.ofNat fee.toNat)))
    (hset : ∀ {fr : Frame}, fr.contract = contract → fr.locals.get? "self" = some (poolRefValue id) →
      fr.locals.get? feeName = some (.int (Int.ofNat fee.toNat)) →
      ExecStmt config fr evm (.internalCall setterName [.storage {base := "self", steps := [.field "slot0"]}, .var feeName] "__c1")
        (.ok {fr with locals := fr.locals.insert "__c1" (wordBytes32Value word)} evm)) :
    ExecFuncBody config f evm (poolSetSlot0Body refName feeName setterName)
      (poolSetSlot0Result (poolSetSlot0Frame f id word refName) evm id word) := by
  let f1 : Frame := {f with locals := f.locals.insert refName (poolRefValue id)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c0" .unit}
  let f3 := poolSetSlot0Frame f id word refName
  have hlet : ExecStmt config f evm (.letStorage refName {base := "self"}) (.ok f1 evm) :=
    ExecStmt.letStorage (resolveStorageAlias hs)
  have hcheck := poolCheckCall (f := f1) (evm := evm) hf (evalLocalValue (store_get_self _ _ _)) "__c0"
  rw [poolSetSlot0Result]
  by_cases hz : poolSqrtPriceWord evm id = ⟨0⟩
  · rw [if_pos hz] at hcheck ⊢
    exact .execBlockRevert (ExecBlock.consNormal hlet (ExecBlock.consRevert hcheck))
  · rw [if_neg hz] at hcheck ⊢
    have hs2 : f2.locals.get? "self" = some (poolRefValue id) :=
      (store_get_ne2 _ _ _ haSelf (by decide : ("__c0" == "self") = false)).trans hs
    have he2 : f2.locals.get? feeName = some (.int (Int.ofNat fee.toNat)) :=
      (store_get_ne2 _ _ _ haFee hcFee).trans he
    have hfee := hset (fr := f2) hf hs2 he2
    have hval := evalLocalValue (cfg := config) (f := f3) (evm := evm) (store_get_self _ _ _)
    have hwrite := poolSlot0_write (f := f3) (evm := evm)
      ((store_get_ne _ _ (by decide : ("__c1" == "self") = false)).trans hs2) word
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp]
      exact .execBlockStatic (ExecBlock.consNormal hlet (ExecBlock.consNormal hcheck
        (ExecBlock.consNormal hfee (ExecBlock.consStatic (ExecStmt.assignStatic hval hwrite hp)))))
    · rw [if_neg hp]
      exact .execBlockOK (ExecBlock.consNormal hlet (ExecBlock.consNormal hcheck
        (ExecBlock.consNormal hfee (ExecBlock.consNormal (ExecStmt.assign hval hwrite) ExecBlock.nil))))

end Benchmarks.UniswapV4PoolManager
