import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralRefine
import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralDecode

/-!
# Morpho `withdrawCollateral((address,address,address,address,uint256),uint256,address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5391; reach lemma `morphoReachWithdrawCollateralBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

/-- `withdrawCollateral((address,address,address,address,uint256),uint256,address,address)`: the theorem `Correct.lean` routes selector 15 to. -/
theorem morphoWithdrawCollateralBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 15)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 15) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some withdrawCollateralTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  obtain ⟨k0, C0, rd0⟩ := morphoReachWithdrawCollateralBody (g := .ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd0
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := morphoBlocks.morpho_block_5391_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd1
    cases hdec : decodeCalldata ["marketParams", "assets", "onBehalf", "receiver"]
        [marketParamsABIType, abiUInt256, abiAddress, abiAddress] I.calldata with
    | none => exact reEquivSelectorDecodingFailed hcode hr hd hdec
    | some args => exact reEquivSelectorRevert hcode hr hd hdec (bodyReverts_nonPayable hcv)
  have rd1 := morphoBlocks.morpho_block_5391_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd0
  rcases morphoWithdrawCollateralDecode (v := v) (R := []) (by decide) hsz hsize rd1 with
    ⟨hbad, hr⟩ | ⟨hb, a2, k2, C2, rd2⟩
  · have hdec : decodeCalldata ["marketParams", "assets", "onBehalf", "receiver"]
        [marketParamsABIType, abiUInt256, abiAddress, abiAddress] I.calldata = none := by
      rw [decodeCalldata_market_uint_two_address_eq, if_neg hbad]
    exact reEquivSelectorDecodingFailed hcode hr hd hdec
  · let p := marketParamsFromCalldata I.calldata
    let assets := calldataWord I.calldata 164
    let account := calldataWord I.calldata 196
    let receiver := calldataWord I.calldata 228
    let evm := initState σ σ₀ (.ofUInt256 g) A I
    have hdec : decodeCalldata ["marketParams", "assets", "onBehalf", "receiver"]
        [marketParamsABIType, abiUInt256, abiAddress, abiAddress] I.calldata =
        some (collateralTransferArgs p assets account receiver) := by
      rw [decodeCalldata_market_uint_two_address_eq, if_pos hb]
      rfl
    have hbound : I.calldata.size < 2 ^ 255 + 4 := by have hh := hb.2.1; omega
    have hc : p.Canonical := hb.2.2.1
    have ha : account.toNat < EVM.addressModulus := hb.2.2.2.1
    have hr : receiver.toNat < EVM.addressModulus := hb.2.2.2.2
    rcases morphoWithdrawCollateralGuards p (R := []) (by decide) ha hr rd2 with
      ⟨hbad, hrev⟩ | ⟨hg, a3, k3, C3, rd3⟩
    · exact reEquivSelectorRevert hcode hrev hd hdec
        (morphoWithdrawCollateralSourceReject p assets account receiver hc ha hr evm (immStore v) hcv hbound hbad)
    · have pref := morphoWithdrawCollateralSourceGuards p assets account receiver hc ha hr evm (immStore v) hcv hbound hg
      have hl := collateralTransferBeforeAccrue_locals p assets account receiver evm (immStore v)
      have ht := morphoWithdrawCollateralRefine p _ (immStore v) hc ha hr hl SourceState.init
        (by exact store_get_self _ _ _) rd3
      cases ht with
      | reverted he hr =>
        exact reEquivSelectorRevert hcode hr hd hdec (ExecFuncBody.execBlockRevert (pref.run he))
      | static he hr =>
        exact reEquivSelectorStatic hcode hr hd hdec (ExecFuncBody.execBlockStatic (pref.run he))
      | ok he hs' hr =>
        exact reEquivSelectorExecutionGen hcode hr hd hdec (ExecFuncBody.execBlockOK (pref.run he))
          hs'.accounts (.fallthrough rfl rfl (by native_decide))

end Benchmarks.Morpho.MorphoBlue
