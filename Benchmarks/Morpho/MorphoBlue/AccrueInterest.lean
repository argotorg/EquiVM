import Benchmarks.Morpho.MorphoBlue.AccruePublicSource
import Benchmarks.Morpho.MorphoBlue.AccruePublicRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

set_option maxRecDepth 10000 in
theorem morphoAccrueInterestXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 1))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 164 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 1) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachAccrueInterestBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_11040_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 160) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 5) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 5) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_11047_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_11040_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert


/-- The public interest-accrual entry point, including calldata validation and all internal outcomes. -/
theorem morphoAccrueInterestBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hd : selectorDispatchMsg contract I.calldata = some accrueInterestTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  let p := marketParamsFromCalldata I.calldata
  by_cases hlen : 164 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc : p.Canonical
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (accrueInterestTransition.params.map Param.name)
            (transitionSignature accrueInterestTransition).paramTypes I.calldata =
            some (createMarketArgs p) := decodeCalldata_marketParams_ok hlen hbound hc
        by_cases hcv : I.weiValue = ⟨0⟩
        · obtain ⟨aw0, k0, C0, rd0⟩ := morphoAccruePublicReachDecode
            (σ := σ) (σ₀ := σ₀) (A := A) (g := .ofUInt256 g) v hcode hsize hsel hcv hlen hbound
          obtain ⟨aw1, k1, C1, rd1⟩ := morphoDecodeMarketParamsOk (v := v) (by simp)
            (by rw [morphoPatchedValidJumps v]; jump_dest) hc rd0
          change RD _ _ _ _ (UInt256.ofNat 11100) [UInt256.ofNat 128, UInt256.ofNat 1211, UInt256.ofNat 0]
            (createMarketDecodedMem p) _ _ _ _ _ at rd1
          by_cases hcreated : marketFieldWord σ I p.id 4 ≠ ⟨0⟩
          · obtain ⟨aw2, k2, C2, rd2⟩ := morphoAccruePublicEnter (v := v) p hcreated rd1
            have hm := (accruePublicMemory p).1
            have hf := morphoAccrueFunctionRefine (v := v) p (immStore v) hc (by simp)
              (SourceState.init (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := .ofUInt256 g))
              (createMarketHeap_morpho hm (by decide) 512 (by decide) (lt_usize _ (by decide)))
              (by decide) hm.params (by decide) (by rw [hm.size]; decide) (by decide)
              (by rw [morphoPatchedValidJumps v]; jump_dest) rd2
            have pref := morphoAccruePublicGuard p hc (initState σ σ₀ (.ofUInt256 g) A I) (immStore v) hcv hbound hcreated
            have hparams := createMarketParams_eval p I.calldata (immStore v) (initState σ σ₀ (.ofUInt256 g) A I)
            have hid := createMarketId_eval p I.calldata (immStore v) (initState σ σ₀ (.ofUInt256 g) A I)
            cases hf with
            | reverted hb hr =>
              apply reEquivSelectorRevert hcode hr hd hdec
              apply ExecFuncBody.execBlockRevert
              apply pref.run
              exact ExecBlock.consRevert (morphoAccrueInternalRevert p _ (immStore v) _
                (.var "marketParams") (.var "id") "__c1" hparams hid hb)
            | static hb hr =>
              apply reEquivSelectorStatic hcode hr hd hdec
              apply ExecFuncBody.execBlockStatic
              apply pref.run
              exact ExecBlock.consStatic (morphoAccrueInternalStatic p _ (immStore v) _
                (.var "marketParams") (.var "id") "__c1" hparams hid hb)
            | @ok frame' evm' value σ' mem' fp' aw' rdata' k' C' hb hv hs' hm' hr =>
              have hcall := morphoAccrueInternalOk p _ (immStore v) _ evm' frame' value
                (.var "marketParams") (.var "id") "__c1" hparams hid hb
              have hsolm : ExecTransitionBody config contract (initState σ σ₀ (.ofUInt256 g) A I)
                  (createMarketArgs p) accrueInterestTransition.body
                  (.returned (resumeAfterInternalCall (createMarketFrame p I.calldata (immStore v)) "__c1" value) evm' none)
                  (immStore v) :=
                ExecFuncBody.execBlockOK (pref.run (ExecBlock.consNormal hcall ExecBlock.nil))
              have hx := morphoBlocks.morpho_block_1211 (immWords := wordsOf (immStore v)) (by simp) hr
              have hx' : RDret (deployedRuntime v) (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) σ' ByteArray.empty := by
                simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hx
              exact reEquivSelectorExecutionGen hcode hx' hd hdec hsolm hs'.accounts
                (.fallthrough rfl rfl (by native_decide))
          · exact reEquivSelectorRevert hcode
              (morphoAccruePublicGuardReverts (v := v) p (not_not.mp hcreated) rd1) hd hdec
              (morphoAccruePublicReject p hc _ (immStore v) hcv hbound (not_not.mp hcreated))
        · exact reEquivSelectorRevert hcode
            (morphoAccrueInterestXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (accrueInterestTransition.params.map Param.name)
            (transitionSignature accrueInterestTransition).paramTypes I.calldata = none :=
          decodeCalldata_marketParams_noncanonical hlen hc
        apply reEquivSelectorDecodingFailed hcode ?_ hd hdec
        by_cases hcv : I.weiValue = ⟨0⟩
        · obtain ⟨aw, k, C, rd⟩ := morphoAccruePublicReachDecode
            (σ := σ) (σ₀ := σ₀) (A := A) (g := .ofUInt256 g) v hcode hsize hsel hcv hlen hbound
          exact morphoDecodeMarketParamsNoncanonical (v := v) (by simp) hc rd
        · exact morphoAccrueInterestXReverts v hcode hsize hsel (.inl hcv)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoAccrueInterestXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_marketParams_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoAccrueInterestXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_marketParams_short (by omega))

end Benchmarks.Morpho.MorphoBlue
