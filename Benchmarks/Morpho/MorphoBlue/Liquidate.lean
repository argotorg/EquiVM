import Benchmarks.Morpho.MorphoBlue.LiquidateRefine
import Benchmarks.Morpho.MorphoBlue.LiquidateDecode

/-!
# Morpho `liquidate((address,address,address,address,uint256),address,uint256,uint256,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1253; reach lemma `morphoReachLiquidateBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

/-- `liquidate((address,address,address,address,uint256),address,uint256,uint256,bytes)`: the theorem `Correct.lean` routes selector 21 to. -/
theorem morphoLiquidateBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 21)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 21) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some liquidateTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  obtain ⟨k0, C0, rd0⟩ := morphoReachLiquidateBody (g := .ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd0
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := morphoBlocks.morpho_block_1253_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd1
    cases hdec : decodeCalldata ["marketParams", "borrower", "seizedAssets", "repaidShares", "data"]
        [marketParamsABIType, abiAddress, abiUInt256, abiUInt256, .bytes] I.calldata with
    | none => exact reEquivSelectorDecodingFailed hcode hr hd hdec
    | some args => exact reEquivSelectorRevert hcode hr hd hdec (bodyReverts_nonPayable hcv)
  have rd1 := morphoBlocks.morpho_block_1253_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd0
  rcases morphoLiquidateDecode (v := v) (R := []) (by decide) hsz hsize rd1 with
    ⟨hbad, hr⟩ | ⟨hb, a2, k2, C2, rd2⟩
  · have hdec : decodeCalldata ["marketParams", "borrower", "seizedAssets", "repaidShares", "data"]
        [marketParamsABIType, abiAddress, abiUInt256, abiUInt256, .bytes] I.calldata = none := by
      rw [decodeCalldata_liquidate_eq, if_neg hbad]
    exact reEquivSelectorDecodingFailed hcode hr hd hdec
  · let p := marketParamsFromCalldata I.calldata
    let account := calldataWord I.calldata 164
    let seized := calldataWord I.calldata 196
    let shares := calldataWord I.calldata 228
    let data := calldataBytesPayload I.calldata (4 + (calldataWord I.calldata 260).toNat)
    let evm := initState σ σ₀ (.ofUInt256 g) A I
    have hdec : decodeCalldata ["marketParams", "borrower", "seizedAssets", "repaidShares", "data"]
        [marketParamsABIType, abiAddress, abiUInt256, abiUInt256, .bytes] I.calldata =
        some (liquidateArgs p account seized shares data) := by
      rw [decodeCalldata_liquidate_eq, if_pos hb]
      rfl
    have hbound : I.calldata.size < 2 ^ 255 + 4 := by have hh := hb.2.1; omega
    have hc : p.Canonical := hb.2.2.1
    have ha : account.toNat < EVM.addressModulus := hb.2.2.2.1
    rcases morphoLiquidateGuards (v := v) p (R := []) (by decide) rd2 with
      ⟨hbad, hr⟩ | ⟨hg, a3, k3, C3, rd3⟩
    · exact reEquivSelectorRevert hcode hr hd hdec
        (morphoLiquidateSourceReject p account seized shares data hc evm (immStore v) hcv hbound hbad)
    · have pref := morphoLiquidateSourceGuards p account seized shares data hc evm (immStore v) hcv hbound hg
      have hl := liquidateBeforeAccrue_locals p account seized shares data evm (immStore v)
      have hstart : (UInt256.ofNat 4 + calldataWord I.calldata 260).toNat =
          4 + (calldataWord I.calldata 260).toNat := add4_word_toNat _ hb.2.2.2.2.1
      have hoff : ((UInt256.ofNat 4 + calldataWord I.calldata 260) + UInt256.ofNat 32).toNat =
          4 + (calldataWord I.calldata 260).toNat + 32 := by
        have hh := hb.2.2.2.2.1
        have hfit : (UInt256.ofNat 4 + calldataWord I.calldata 260).toNat + 32 < UInt256.size := by
          rw [hstart]; norm_num [solcMaxU64, UInt256.size] at hh ⊢; omega
        rw [uadd_word_ofNat_toNat _ 32 hfit, hstart]
      have hbytes := hb.2.2.2.2.2
      have ht := morphoLiquidateRefine (v := v) p _ (immStore v) hc ha rfl hl SourceState.init
        (by exact store_get_self _ _ _) hbytes.2.1 (by rw [hoff]; exact hbytes.2.2)
        (by rw [hoff]; exact calldataBytesPayload_read hbytes) (calldataBytesPayload_size hbytes) rd3
      cases ht with
      | reverted he hr =>
        exact reEquivSelectorRevert hcode hr hd hdec (ExecFuncBody.execBlockRevert (pref.run he))
      | static he hr =>
        exact reEquivSelectorStatic hcode hr hd hdec (ExecFuncBody.execBlockStatic (pref.run he))
      | ok he hs' henc hr =>
        exact reEquivSelectorExecutionGen hcode hr hd hdec (ExecFuncBody.execBlockRet (pref.run he))
          hs'.accounts (.returned rfl henc)

end Benchmarks.Morpho.MorphoBlue
