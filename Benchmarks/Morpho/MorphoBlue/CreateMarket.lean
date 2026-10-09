import Benchmarks.Morpho.MorphoBlue.CreateMarketFinish
import Benchmarks.Morpho.MorphoBlue.CreateMarketStatic

/-!
# Morpho `createMarket((address,address,address,address,uint256))`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4600; reach lemma `morphoReachCreateMarketBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

set_option maxRecDepth 10000 in
theorem morphoCreateMarketXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 16))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 164 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 16) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachCreateMarketBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_4600_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 160) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 5) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 5) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_4607_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_4600_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert


/-- `createMarket((address,address,address,address,uint256))`: the theorem `Correct.lean` routes selector 16 to. -/
theorem morphoCreateMarketBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 16)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hd : selectorDispatchMsg contract I.calldata = some createMarketTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  let p := marketParamsFromCalldata I.calldata
  by_cases hlen : 164 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc : p.Canonical
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (createMarketTransition.params.map Param.name)
            (transitionSignature createMarketTransition).paramTypes I.calldata =
            some (createMarketArgs p) := decodeCalldata_marketParams_ok hlen hbound hc
        by_cases hcv : I.weiValue = ⟨0⟩
        · obtain ⟨aw0, k0, C0, rd0⟩ := morphoCreateMarketReachDecode
            (σ := σ) (σ₀ := σ₀) (A := A) (g := .ofUInt256 g) v hcode hsize hsel hcv hlen hbound
          obtain ⟨aw1, k1, C1, rd1⟩ := morphoDecodeMarketParamsOk (v := v) (by simp)
            (by rw [morphoPatchedValidJumps v]; jump_dest) hc rd0
          change RD _ _ _ _ (UInt256.ofNat 4657) [UInt256.ofNat 128, UInt256.ofNat 0]
            (createMarketDecodedMem p) _ _ _ _ _ at rd1
          by_cases hguards : createMarketIrmByte σ I p ≠ ⟨0⟩ ∧
              createMarketLltvByte σ I p ≠ ⟨0⟩ ∧ marketFieldWord σ I p.id 4 = ⟨0⟩
          · obtain ⟨hi, hl, hn⟩ := hguards
            obtain ⟨aw2, k2, C2, rd2⟩ := morphoCreateMarketReachStore (v := v) p hc hi hl hn rd1
            by_cases hp : I.perm = true
            · obtain ⟨aw3, k3, C3, rd3⟩ := morphoCreateMarketStoreFirst (v := v) p hp rd2
              obtain ⟨aw4, k4, C4, rd4⟩ := morphoCreateMarketStoreRest (v := v) p hc hp rd3
              have hs := createMarketStored_bridge
                (SourceState.init (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := .ofUInt256 g)) p
              by_cases hi0 : p.irm = ⟨0⟩
              · have hx := morphoCreateMarketNoIrmReturns (v := v) p hc hp hi0 rd4
                have hb := morphoCreateMarketSourceNoIrm p hc
                  (initState σ σ₀ (.ofUInt256 g) A I) (immStore v) hcv hbound hi hl hn hi0
                exact reEquivSelectorExecutionGen hcode hx hd hdec hb hs.accounts
                  (.fallthrough rfl rfl (by native_decide))
              · obtain ⟨mem, aw5, gasArg, k5, C5, hcd, rd5⟩ :=
                  morphoCreateMarketReachCall (v := v) p hc hp hi0 rd4
                obtain ⟨evm', z, out, hcall, hs', hout, hx⟩ :=
                  morphoCreateMarketCall (v := v) p hc hs hp (by decide) hcd rd5
                have hb := morphoCreateMarketSourceCall p hc
                  (initState σ σ₀ (.ofUInt256 g) A I) (immStore v) hcv hbound hi hl hn hi0
                  evm' z out (by simpa only [hs.env, ← hs.accounts] using hcall) hout
                by_cases hgood : z = true ∧ 32 ≤ out.size
                · rw [if_pos hgood] at hb hx
                  obtain ⟨frame, hb⟩ := hb
                  exact reEquivSelectorExecutionGen hcode hx hd hdec hb rfl
                    (.fallthrough rfl rfl (by native_decide))
                · rw [if_neg hgood] at hb hx
                  exact reEquivSelectorRevert hcode hx hd hdec hb
            · have hpf : I.perm = false := Bool.eq_false_of_not_eq_true hp
              exact reEquivSelectorStatic hcode
                (morphoCreateMarketStoreStatic (v := v) (by simp) hpf rd2) hd hdec
                (morphoCreateMarketSourceStatic p hc _ (immStore v) hcv hbound hi hl hn hpf)
          · have hbad : createMarketIrmByte σ I p = ⟨0⟩ ∨
                createMarketLltvByte σ I p = ⟨0⟩ ∨ marketFieldWord σ I p.id 4 ≠ ⟨0⟩ := by
              simpa only [not_and_or, not_not] using hguards
            exact reEquivSelectorRevert hcode
              (morphoCreateMarketGuardReverts (v := v) p hc hbad rd1) hd hdec
              (morphoCreateMarketSourceRejects p hc _ (immStore v) hcv hbound hbad)
        · exact reEquivSelectorRevert hcode
            (morphoCreateMarketXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (createMarketTransition.params.map Param.name)
            (transitionSignature createMarketTransition).paramTypes I.calldata = none :=
          decodeCalldata_marketParams_noncanonical hlen hc
        apply reEquivSelectorDecodingFailed hcode ?_ hd hdec
        by_cases hcv : I.weiValue = ⟨0⟩
        · obtain ⟨aw, k, C, rd⟩ := morphoCreateMarketReachDecode
            (σ := σ) (σ₀ := σ₀) (A := A) (g := .ofUInt256 g) v hcode hsize hsel hcv hlen hbound
          exact morphoDecodeMarketParamsNoncanonical (v := v) (by simp) hc rd
        · exact morphoCreateMarketXReverts v hcode hsize hsel (.inl hcv)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoCreateMarketXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_marketParams_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoCreateMarketXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_marketParams_short (by omega))

end Benchmarks.Morpho.MorphoBlue
