import Benchmarks.Morpho.MorphoBlue.AuthorizationSigFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def storeAuthorizationEnabled (evm : EVM.State) (a : AuthorizationWords) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (authorizationSlot a.authorizer a.authorized)
    (setBoolOffset0Word (EVM.storageLoad evm evm.executionEnv.codeOwner
      (authorizationSlot a.authorizer a.authorized)) a.enabled)

theorem morphoAuthorizationSourceFinish {a cd locals} (hl : AuthorizationLocals a cd locals)
    (imms : Store) (evm : EVM.State) (hc : a.Canonical) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (setAuthorizationWithSigTransition.body.drop 24)
      (.returned { contract := contract, locals := locals, immutables := imms }
        (storeAuthorizationEnabled evm a) (some [.bytes ByteArray.empty])) := by
  have h0 (st : EVM.State) : evalExpr? config
      { contract := contract, locals := locals, immutables := imms } st
      (.tupleGet (.var "authorization") 0) = .ok (.address (AccountAddress.ofNat a.authorizer.toNat)) :=
    by simpa only [AuthorizationWords.fieldValue] using hl.evalField imms st ⟨0, by decide⟩
  have h1 (st : EVM.State) : evalExpr? config
      { contract := contract, locals := locals, immutables := imms } st
      (.tupleGet (.var "authorization") 1) = .ok (.address (AccountAddress.ofNat a.authorized.toNat)) :=
    by simpa only [AuthorizationWords.fieldValue] using hl.evalField imms st ⟨1, by decide⟩
  have h2 (st : EVM.State) : evalExpr? config
      { contract := contract, locals := locals, immutables := imms } st
      (.tupleGet (.var "authorization") 2) = .ok (wordToElem .bool a.enabled) := by
    simpa only [AuthorizationWords.fieldValue, wordToElemBool, decide_not] using hl.evalField imms st ⟨2, by decide⟩
  have h3 (st : EVM.State) : evalExpr? config
      { contract := contract, locals := locals, immutables := imms } st
      (.tupleGet (.var "authorization") 3) = .ok (.int (Int.ofNat a.nonce.toNat)) :=
    by simpa only [AuthorizationWords.fieldValue] using hl.evalField imms st ⟨3, by decide⟩
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
    .address (AccountAddress.ofNat a.authorizer.toNat), .int (Int.ofNat a.nonce.toNat)]) ?_)
  · apply ExecBlock.consNormal (ExecStmt.assign (h2 evm)
      (assignMorphoIsAuthorized evm locals imms _ _ a.authorizer a.authorized a.enabled
        hl.authorized (h0 evm) (h1 evm) hc.1 hc.2.1))
    apply ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
      .address (AccountAddress.ofNat a.authorizer.toNat), .address (AccountAddress.ofNat a.authorized.toNat),
      wordToElem .bool a.enabled]) ?_)
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      have hr := evalCalldataSlice (cfg := config) (evm := storeAuthorizationEnabled evm a)
        (frame := { contract := contract, locals := locals, immutables := imms }) hl.calldata
        (by decide : 0 ≤ 0) (Nat.zero_le cd.size)
      change evalExpr? config _ _ (.bytesSlice (.var "__calldata") (.intLit 0) (.intLit 0)) = _ at hr
      dsimp only [storeAuthorizationEnabled] at hr
      simp [evalExprs?, hr, bind, EvalResult.bind, pure]
    · simp only [evalExprs?, h0, h1, h2, evalExpr?, envValue, pure, bind, EvalResult.bind,
        storageStore_executionEnv]
  · simp only [evalExprs?, h0, h3, evalExpr?, envValue, pure, bind, EvalResult.bind]


theorem authorizationFinalSourceState {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (a : AuthorizationWords) :
    SourceState s0 ee (authorizationFinalAccounts a σ ee) (storeAuthorizationEnabled evm a) := by
  have hw := hs.readModifyWrite (authorizationSlot a.authorizer a.authorized)
    (fun old ↦ setBoolOffset0Word old a.enabled)
  simpa only [storeAuthorizationEnabled, authorizationFinalAccounts, solcSlotWordAt] using hw

end Benchmarks.Morpho.MorphoBlue
