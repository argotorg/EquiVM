import Examples.TinyImmutable.Constructor
import Examples.TinyImmutable.Owner
import Examples.TinyImmutable.Quote
import Examples.TinyImmutable.Scale
import Reasoning.Dispatch
import Reasoning.SolmBody
import Solm.Equiv

/-!
# TinyImmutable correctness stub

This is the small immutable-aware analogue of the UniswapV3 benchmark statement: for each immutable
assignment `v`, the deployed runtime is the solc template patched with `v`, and runtime equivalence
is stated against `contract v`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables

namespace TinyImmutable

theorem tinyBodyReverts_nonPayable (v : TinyImmutables) (t : TransitionDecl)
    (ht : t ∈ (contract v).transitions) (evm : EVM.State) (callargs : Store)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm callargs t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl <;> exact bodyReverts_nonPayable hwv

theorem tinyNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : TinyImmutables) (hcode : I.code = patchedRuntime v) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (tinyX_callvalue_ne (g := Sat256.ofUInt256 g) v hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg (contract v) I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ (contract v).transitions := by
          rw [dispatchMsg_eq_dispatchList (contract v) I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode (config v).abiDecodeMode
            (t.params.map Param.name) (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (tinyBodyReverts_nonPayable v t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem tinyImmutableCorrect (v : TinyImmutables) {code : ByteArray}
    (hcode : patchRuntime tinyImmutableBytecode (patches v) = some code) :
    runtimeEquivalence!?! (config v) code (contract v) := by
  have hcode' := code_eq_patchedRuntime_of_patch (v := v) hcode
  subst code
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hIcode hsize _hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hshort : I.calldata.size < 4
    · exact (tinyX_short (g := Sat256.ofUInt256 g) v hIcode hwv hshort)
        |>.reEquivNoDispatch hIcode (tinyDispatch_none_short v hshort)
    · have hsz4 : 4 ≤ I.calldata.size := by omega
      by_cases howner : (ownerSelBytes == I.calldata.extract 0 4) = true
      · exact tinyOwnerBodyCore v hIcode hsize hwv howner hAccounts
      · have hownerF : (ownerSelBytes == I.calldata.extract 0 4) = false :=
          Bool.eq_false_of_not_eq_true howner
        by_cases hquote : (quoteSelBytes == I.calldata.extract 0 4) = true
        · exact tinyQuoteBodyCore v hIcode hsize hwv hownerF hquote hAccounts
        · have hquoteF : (quoteSelBytes == I.calldata.extract 0 4) = false :=
            Bool.eq_false_of_not_eq_true hquote
          by_cases hscale : (scaleSelBytes == I.calldata.extract 0 4) = true
          · exact tinyScaleBodyCore v hIcode hsize hwv hownerF hquoteF hscale hAccounts
          · have hscaleF : (scaleSelBytes == I.calldata.extract 0 4) = false :=
              Bool.eq_false_of_not_eq_true hscale
            exact (tinyX_noMatch (g := Sat256.ofUInt256 g) v hIcode hwv hsz4 hsize
                hownerF hquoteF hscaleF)
              |>.reEquivNoDispatch hIcode
                (tinyDispatch_none_nomatch v hownerF hquoteF hscaleF)
  · exact tinyNonPayable v hIcode hwv

theorem tinyImmutableContractCorrect (v : TinyImmutables) {code : ByteArray}
    (hcode : patchRuntime tinyImmutableBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) tinyImmutableCreationBytecode code (contract v)
      (runtimeCodeOf tinyImmutableBytecode) :=
  contractEquivalenceWith.intro (tinyImmutableConstructorCorrect v)
    (tinyImmutableCorrect v hcode)

end TinyImmutable
