import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetReservesEvm
import Benchmarks.CompoundIII.Comet.ReservesExternal

/-!
# CometWithExtendedAssetList `getReserves()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1375; reach lemma `cometWithExtendedAssetListReachGetReservesBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

/-- `getReserves()`: the theorem `Correct.lean` routes selector 1 to. -/
theorem cometWithExtendedAssetListGetReservesBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 1) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some getReservesTransition :=
    cometSelectorDispatch ⟨1, by decide⟩ hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (getReservesTransition.params.map Param.name)
      (transitionSignature getReservesTransition).paramTypes I.calldata = some (∅ : Store) :=
    decodeCalldataWithMode_empty_ok hsz
  have hX := getReservesX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hindices : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I)
          (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)
      · unfold GetReservesResult at hX
        rw [if_pos ⟨hv, hhi, hindices⟩] at hX
        obtain ⟨evm', σ', z, out, hcall, haccounts, hout, hr⟩ := hX
        have hout' : out.size < 2^255 := lt_trans hout (by decide)
        by_cases hvalid : ReservesReplyValid v (solcSlotWordAt ⟨0⟩ σ I)
            (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I) z out
        · rw [if_pos hvalid] at hr
          obtain ⟨frame, hbody⟩ := getReserves_returns v evm' z out hv hhi hindices
            hcall hout' hvalid
          apply selectorStateReturn_refines hcode hr hd hdec hbody haccounts
          apply returnEquiv_of_encode
          rw [← reservesWord_signed hindices hvalid.2.2]
          exact signedWordReturnEncoding _
        · rw [if_neg hvalid] at hr
          exact selectorRevert_refines hcode hr hd hdec
            (getReserves_reverts v evm' z out hv hhi hindices hcall hout' hvalid)
      · simp only [GetReservesResult, hindices, and_false, if_false] at hX
        exact selectorRevert_refines hcode hX hd hdec (getReserves_early_revert v hv hhi hindices)
    · simp only [GetReservesResult, hhi, false_and, and_false, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [getReservesTransition_body]
      exact calldataPrologue_huge hv hhi
  · simp only [GetReservesResult, hv, false_and, if_false] at hX
    apply selectorRevert_refines hcode hX hd hdec
    rw [getReservesTransition_body]
    exact calldataPrologue_nonpayable hv

end Benchmarks.CompoundIII.Comet
