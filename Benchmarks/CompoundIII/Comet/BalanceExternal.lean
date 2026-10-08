import Benchmarks.CompoundIII.Comet.BalanceSource
import Benchmarks.CompoundIII.Comet.AddressGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem balanceTransition_body : balanceOfTransition.body = calldataPrologue
    [.internalCall "balanceOf_body" [.var "account"] "result", .return [.var "result"]] := rfl

theorem getBalance_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hvalid : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I)
      (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "account" I) balanceOfTransition.body
      (.returned frame (initState σ σ₀ g A I)
        (some [.int (balanceWord v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
          (timestampWord I)
          (userBasicWord σ I (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).toNat]))
      (immStore v) := by
  let addr := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "account" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "account") =
      .ok (.address addr) := by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs := balance_call_ok v frame (initState σ σ₀ g A I) addr _ "result" rfl rfl he
    (by simpa only [storageLoad_initState_solcSlotWord, solcSlotWordAt] using hvalid)
  dsimp only at hs
  simp only [storageLoad_initState_solcSlotWord] at hs
  rw [balanceTransition_body]
  refine ⟨{ frame with locals := frame.locals.insert "result" (.int (balanceWord v
    (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)
      (userBasicWord σ I addr)).toNat) }, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal hs
  exact ABlock.start.returns (by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl)

theorem getBalance_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hvalid : ¬ CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I)
      (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "account" I) balanceOfTransition.body .reverted (immStore v) := by
  let addr := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "account" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "account") =
      .ok (.address addr) := by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  rw [balanceTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert
    (balance_call_revert v frame (initState σ σ₀ g A I) addr _ "result" rfl rfl he
      (by simpa only [storageLoad_initState_solcSlotWord, solcSlotWordAt] using hvalid))

end Benchmarks.CompoundIII.Comet
