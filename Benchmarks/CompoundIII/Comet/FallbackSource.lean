import Benchmarks.CompoundIII.Comet.DelegateCallBridge
import Benchmarks.CompoundIII.Comet.SourceSelectors

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def fallbackTransition : TransitionDecl :=
  { name := "fallback", params := [{ name := "data", ty := .bytes }], returnType := [.bytes],
    body := [
      .letDecl "delegate" (some (.elem .address)) (.immutable "extensionDelegate"),
      .delegateCall (.var "delegate") (.var "data") "ok" "result",
      .require (.var "ok"),
      .return [.var "result"]] }

theorem contract_fallback : contract.fallback = some fallbackTransition := rfl

theorem cometFallbackNoSelector {cd : ByteArray}
    (hnm : ∀ i, i < 68 → (cometWithExtendedAssetListSelBytes i == cd.extract 0 4) = false) :
    selectorDispatchMsg contract cd = none := by
  rw [selectorDispatchMsg_eq_dispatchList]
  apply dispatchList_none_of_all_ne
  intro t ht
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ht
  let j' : Fin 68 := ⟨j.val, j.isLt⟩
  have hh : transitionAt j' = t := hj
  rw [← hh, selectorOf_transitionAt]
  exact hnm j'.val j'.isLt

theorem cometFallbackNoReceive (cd : ByteArray) : receiveDispatchMsg contract cd = none := by
  simp only [receiveDispatchMsg, show contract.receive = none from rfl, ite_self]

def fallbackArgs (cd : ByteArray) : Store := (∅ : Store).insert "data" (.bytes cd)

def fallbackDelegateFrame (v : CometWithExtendedAssetListImmutables) (cd : ByteArray) : Frame :=
  { contract := contract, immutables := immStore v,
    locals := (fallbackArgs cd).insert "delegate" (.address v.extensionDelegate) }

def fallbackResultFrame (v : CometWithExtendedAssetListImmutables) (cd : ByteArray)
    (z : Bool) (out : ByteArray) : Frame :=
  { fallbackDelegateFrame v cd with locals :=
    ((fallbackDelegateFrame v cd).locals.insert "ok" (.bool z)).insert "result" (.bytes out) }

theorem cometFallbackSource {v : CometWithExtendedAssetListImmutables} {evm evm' : State}
    {cd out : ByteArray} {z : Bool}
    (hc : delegateCallViaEVM evm v.extensionDelegate cd (z, evm', out)) :
    ExecTransitionBody config contract evm (fallbackArgs cd) fallbackTransition.body
      (if z then .returned (fallbackResultFrame v cd z out) evm' (some [.bytes out])
       else .reverted) (immStore v) := by
  have hlet : ExecStmt config
      { contract := contract, locals := fallbackArgs cd, immutables := immStore v } evm
      (.letDecl "delegate" (some (.elem .address)) (.immutable "extensionDelegate"))
      (.ok (fallbackDelegateFrame v cd) evm) :=
    ExecStmt.letDecl (evalImmutable_extensionDelegate config contract (fallbackArgs cd) evm v)
  have hcall : ExecStmt config (fallbackDelegateFrame v cd) evm
      (.delegateCall (.var "delegate") (.var "data") "ok" "result")
      (.ok (fallbackResultFrame v cd z out) evm') := by
    apply delegateCallSource ?_ ?_ hc
    · simp only [evalExpr?, fallbackDelegateFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]
      rfl
    · simp only [evalExpr?, fallbackDelegateFrame, fallbackArgs,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl
  have hok : evalExpr? config (fallbackResultFrame v cd z out) evm' (.var "ok") =
      .ok (.bool z) := by
    simp only [evalExpr?, fallbackResultFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  cases z with
  | false =>
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal hlet
      (ExecBlock.consNormal hcall (ExecBlock.consRevert (ExecStmt.requireFalse hok))))
  | true =>
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal hlet
    apply ExecBlock.consNormal hcall
    apply ExecBlock.consNormal (ExecStmt.requireTrue hok)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, fallbackResultFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl

end Benchmarks.CompoundIII.Comet
