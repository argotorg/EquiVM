import Benchmarks.CompoundIII.Comet.ReservesSource
import Benchmarks.CompoundIII.Comet.CheckedGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem getReservesTransition_body :
    getReservesTransition.body = calldataPrologue
      [.internalCall "getReserves_body" [] "__r", .return [.var "__r"]] := rfl

theorem getReserves_early_revert {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (hv : I.weiValue = ⟨0⟩)
    (hhi : I.calldata.size < 2^255 + 4)
    (hvalid : ¬ CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
      (timestampWord I)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      getReservesTransition.body .reverted (immStore v) := by
  let frame := calldataLocalFrame { contract := contract, locals := ∅, immutables := immStore v }
    (initState σ σ₀ g A I)
  rw [getReservesTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consRevert
  exact reserves_call_early_revert v frame (initState σ σ₀ g A I) "__r" rfl rfl
    (by simpa only [storageLoad_initState_solcSlotWord, solcSlotWordAt] using hvalid)

theorem getReserves_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hindices : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
      (timestampWord I))
    (hc : callViaEVM (initState σ σ₀ g A I) v.baseToken 0 (tokenBalancePayload I.codeOwner)
      (z, evm', out) false) (hsize : out.size < 2^255)
    (hvalid : ReservesReplyValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
      (timestampWord I) z out) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      getReservesTransition.body (.returned frame evm'
        (some [.int (reservesValue v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
          (timestampWord I) (calldataWord out 0))])) (immStore v) := by
  let frame := calldataLocalFrame { contract := contract, locals := ∅, immutables := immStore v }
    (initState σ σ₀ g A I)
  have hs := reserves_call_result v frame (initState σ σ₀ g A I) evm' "__r" z out rfl rfl
    (by simpa only [storageLoad_initState_solcSlotWord] using hindices) hc hsize
  dsimp only at hs
  simp only [storageLoad_initState_solcSlotWord] at hs
  simp only [show (initState σ σ₀ g A I).executionEnv = I from rfl] at hs
  simp only [solcSlotWordAt] at hvalid
  rw [if_pos hvalid] at hs
  rw [getReservesTransition_body]
  refine ⟨{ frame with locals :=
    frame.locals.insert "__r" (.int (reservesValue v (solcSlotWordAt ⟨0⟩ σ I)
      (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I) (calldataWord out 0))) }, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal hs
  exact ABlock.start.returns (by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl)

theorem getReserves_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hindices : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
      (timestampWord I))
    (hc : callViaEVM (initState σ σ₀ g A I) v.baseToken 0 (tokenBalancePayload I.codeOwner)
      (z, evm', out) false) (hsize : out.size < 2^255)
    (hvalid : ¬ ReservesReplyValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
      (timestampWord I) z out) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      getReservesTransition.body .reverted (immStore v) := by
  let frame := calldataLocalFrame { contract := contract, locals := ∅, immutables := immStore v }
    (initState σ σ₀ g A I)
  have hs := reserves_call_result v frame (initState σ σ₀ g A I) evm' "__r" z out rfl rfl
    (by simpa only [storageLoad_initState_solcSlotWord] using hindices) hc hsize
  dsimp only at hs
  simp only [storageLoad_initState_solcSlotWord] at hs
  simp only [show (initState σ σ₀ g A I).executionEnv = I from rfl] at hs
  simp only [solcSlotWordAt] at hvalid
  rw [if_neg hvalid] at hs
  rw [getReservesTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert hs

end Benchmarks.CompoundIII.Comet
