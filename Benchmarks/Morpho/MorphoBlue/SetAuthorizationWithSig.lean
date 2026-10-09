import Benchmarks.Morpho.MorphoBlue.AuthorizationSigRefine
import Benchmarks.Morpho.MorphoBlue.RawFallbackRefine

/-!
# Morpho `setAuthorizationWithSig((address,address,bool,uint256,uint256),(uint8,bytes32,bytes32))`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5759; reach lemma `morphoReachSetAuthorizationWithSigBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

/-- `setAuthorizationWithSig((address,address,bool,uint256,uint256),(uint8,bytes32,bytes32))`: the theorem `Correct.lean` routes selector 27 to. -/
theorem morphoSetAuthorizationWithSigBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 27)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 27) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = none := by
    apply morphoSelectorDispatch_none_of_misses
    intro i hi
    rw [← byteArray_eq_of_beq hsel]
    interval_cases i <;> decide +kernel
  have hreceive : receiveDispatchMsg contract I.calldata = none := by
    simp [receiveDispatchMsg, show contract.receive = none from rfl]
  obtain ⟨k, C, rd⟩ := morphoReachSetAuthorizationWithSigBody (g := .ofUInt256 g)
    (σ := σ) (σ₀ := σ₀) (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd0 := morphoBlocks.morpho_block_5759_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd0
    exact reEquivRawFallbackRevert hcode hr hd hreceive rfl rfl rfl (bodyReverts_nonPayable hcv)
  have rd0 := morphoBlocks.morpho_block_5759_fallthrough (immWords := wordsOf (immStore v))
    (by decide) hcv rd
  rcases morphoAuthorizationSigDecode (v := v) (by decide) hsz hsize rd0 with
    ⟨hbad, hr⟩ | ⟨hb, aw1, k1, C1, rd1⟩
  · exact reEquivRawFallbackRevert hcode hr hd hreceive rfl rfl rfl
      (morphoAuthorizationSigSourceDecodeRevert _ v hcv hsel hbad)
  · let evm := initState σ σ₀ (.ofUInt256 g) A I
    let a := authorizationFromCalldata I.calldata
    have pref := morphoAuthorizationSigSourceDecode evm v hcv hsel hb
    have hl := authorizationDecodedFrame_locals I.calldata v
    have hn := morphoAuthorizationNonceRefine (v := v) a I.calldata _ (immStore v)
      hb.2.2 hl SourceState.init (by decide) rd1
    have ht : RawReturnBlockRefines config (deployedRuntime v) I (.ofUInt256 g) evm
        (authorizationDecodedFrame I.calldata v) evm
        (setAuthorizationWithSigTransition.body.drop 10) := by
      cases hn with
      | reverted he hr => exact .reverted he hr
      | static he hr => exact .static he hr
      | ok p hl' hs' hp rd' =>
        exact (morphoAuthorizationSignatureRefine (v := v) a _ hb.2.2 hb.1 hl' hs'
          (by decide) hp rd').prepend p
    exact (ht.prepend (StateBlock.ofABlock pref)).fallback hcode hd hreceive rfl rfl rfl

end Benchmarks.Morpho.MorphoBlue
