import Benchmarks.Morpho.MorphoBlue.SetFeeGuards
import Benchmarks.Morpho.MorphoBlue.SetFeeFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

set_option maxRecDepth 10000 in
theorem morphoSetFeeXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 4))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 196 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 4) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachSetFeeBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_9582_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 192) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 6) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 6) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_9589_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_9582_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert


theorem morphoSetFeeReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 4)) (hcv : I.weiValue = ⟨0⟩)
    (hlen : 196 ≤ I.calldata.size) (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11655)
      [UInt256.ofNat 9639, UInt256.ofNat 128, UInt256.ofNat 0]
      (marketParamsAllocatedMem solcFreePtrMem) aw ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachSetFeeBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd
  have rd0 := morphoBlocks.morpho_block_9582_fallthrough (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_9582_fallthrough_stack]) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 6) hlen hbound hsize
  have rd1 := morphoBlocks.morpho_block_9589_fallthrough (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_9582_fallthrough_stack])
    (by simpa only [wordAddNegFour] using hcond) rd0
  have rd2 := morphoBlocks.morpho_block_9631 (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_9582_fallthrough_stack])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hfp : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  obtain ⟨aw, k', C', rd3⟩ := morphoDecodeMarketParamsPrefix (v := v) (by simp [morphoBlocks.morpho_block_9582_fallthrough_stack])
    hsize (by omega) hbound (by rw [hfp]; decide) rd2
  refine ⟨aw, k', C', ?_⟩
  simpa only [hfp] using rd3

/-- `setFee((address,address,address,address,uint256),uint256)`: the theorem `Correct.lean` routes selector 4 to. -/
theorem morphoSetFeeBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hd : selectorDispatchMsg contract I.calldata = some setFeeTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  let p := marketParamsFromCalldata I.calldata
  let fee := calldataWord I.calldata 164
  by_cases hlen : 196 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc : p.Canonical
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (setFeeTransition.params.map Param.name)
            (transitionSignature setFeeTransition).paramTypes I.calldata =
            some (setFeeArgs p fee) := decodeCalldata_marketParams_uint256_ok hlen hbound hc
        by_cases hcv : I.weiValue = ⟨0⟩
        · obtain ⟨aw0, k0, C0, rd0⟩ := morphoSetFeeReachDecode
            (σ := σ) (σ₀ := σ₀) (A := A) (g := .ofUInt256 g) v hcode hsize hsel hcv hlen hbound
          obtain ⟨aw1, k1, C1, rd1⟩ := morphoDecodeMarketParamsOk (v := v) (by simp)
            (by rw [morphoPatchedValidJumps v]; jump_dest) hc rd0
          change RD _ _ _ _ (UInt256.ofNat 9639) [UInt256.ofNat 128, UInt256.ofNat 0]
            (createMarketDecodedMem p) _ _ _ _ _ at rd1
          by_cases hg : SetFeeGuards σ I p fee
          · obtain ⟨aw2, k2, C2, rd2⟩ := morphoSetFeeEnter (v := v) p hg rd1
            have hm := (setFeeLimitHeap p).1
            have hf := morphoAccrueFunctionRefine (v := v) p (immStore v) hc
              (by simp [setFeeAccrueTail])
              (SourceState.init (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := .ofUInt256 g))
              (createMarketHeap_morpho hm (by decide) 512 (by decide) (lt_usize _ (by decide)))
              (by decide) hm.params (by decide) (by rw [hm.size]; decide) (by decide)
              (by rw [morphoPatchedValidJumps v]; jump_dest) rd2
            have pref := morphoSetFeeSourceGuards p fee hc (initState σ σ₀ (.ofUInt256 g) A I)
              (immStore v) hcv hbound hg
            have hl := setFeeFrame_market p fee I.calldata (immStore v)
            have hparams := hl.evalParams (immStore v) (initState σ σ₀ (.ofUInt256 g) A I)
            have hid := hl.evalId (immStore v) (initState σ σ₀ (.ofUInt256 g) A I)
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
              let frame := resumeAfterInternalCall (setFeeFrame p fee I.calldata (immStore v)) "__c1" value
              have hl' : MarketLocals p frame.locals := hl.insert "__c1" _ (by decide)
              have hg' : frame.locals.get? "newFee" = some (.int (Int.ofNat fee.toNat)) := by
                change (((setFeeFrame p fee I.calldata (immStore v)).locals).insert "__c1" _).get? "newFee" = _
                rw [store_get_ne _ _ (by decide)]
                exact setFeeFrame_get_fee p fee I.calldata (immStore v)
              by_cases hp : I.perm = true
              · have hx := morphoSetFeeFinish (v := v) p.id fee hp
                  (by have hfit := hg.2.2.2; unfold maxMarketFee at hfit; omega) hr
                have hsfinal := storeMarketField_bridge hs' p.id ⟨5, by decide⟩ fee
                have hsolm : ExecTransitionBody config contract (initState σ σ₀ (.ofUInt256 g) A I)
                    (setFeeArgs p fee) setFeeTransition.body
                    (.returned frame (storeMarketField evm' p.id ⟨5, by decide⟩ fee) none) (immStore v) := by
                  apply ExecFuncBody.execBlockOK
                  apply pref.run
                  apply ExecBlock.consNormal hcall
                  exact morphoSetFeeFinishSource p fee frame.locals (immStore v) evm' hl' hg' hg.2.2.2
                exact reEquivSelectorExecutionGen hcode hx hd hdec hsolm hsfinal.accounts
                  (.fallthrough rfl rfl (by native_decide))
              · have hp' : I.perm = false := Bool.eq_false_iff.mpr hp
                apply reEquivSelectorStatic hcode (morphoSetFeeFinishStatic (v := v) (by simp) hp' hr) hd hdec
                apply ExecFuncBody.execBlockStatic
                apply pref.run
                apply ExecBlock.consNormal hcall
                exact ExecBlock.consStatic (execStmt_assign_static
                  (morphoSetFeeAssign p fee frame.locals (immStore v) evm' hl' hg' hg.2.2.2)
                  (by rw [hs'.env]; exact hp'))
          · exact reEquivSelectorRevert hcode (morphoSetFeeGuardReverts (v := v) p hg rd1) hd hdec
              (morphoSetFeeSourceRejects p fee hc _ (immStore v) hcv hbound hg)
        · exact reEquivSelectorRevert hcode
            (morphoSetFeeXReverts v hcode hsize hsel (.inl hcv)) hd hdec (bodyReverts_nonPayable hcv)
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (setFeeTransition.params.map Param.name)
            (transitionSignature setFeeTransition).paramTypes I.calldata = none :=
          decodeCalldata_marketParams_uint256_noncanonical hlen hc
        apply reEquivSelectorDecodingFailed hcode ?_ hd hdec
        by_cases hcv : I.weiValue = ⟨0⟩
        · obtain ⟨aw, k, C, rd⟩ := morphoSetFeeReachDecode
            (σ := σ) (σ₀ := σ₀) (A := A) (g := .ofUInt256 g) v hcode hsize hsel hcv hlen hbound
          exact morphoDecodeMarketParamsNoncanonical (v := v) (by simp) hc rd
        · exact morphoSetFeeXReverts v hcode hsize hsel (.inl hcv)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoSetFeeXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_marketParams_uint256_badSize (.inr (by omega)))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoSetFeeXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_marketParams_uint256_badSize (.inl (by omega)))

end Benchmarks.Morpho.MorphoBlue
