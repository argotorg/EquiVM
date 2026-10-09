import Benchmarks.Morpho.MorphoBlue.WithdrawRefine
import Benchmarks.Morpho.MorphoBlue.MarketTwoWordsTwoAddressesDecode

/-!
# Morpho `withdraw((address,address,address,address,uint256),uint256,uint256,address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7496; reach lemma `morphoReachWithdrawBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

/-- `withdraw((address,address,address,address,uint256),uint256,uint256,address,address)`: the theorem `Correct.lean` routes selector 10 to. -/
theorem morphoWithdrawBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 10)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 10) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some withdrawTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  obtain ⟨k0, C0, rd0⟩ := morphoReachWithdrawBody (g := .ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd0
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := morphoBlocks.morpho_block_7496_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd1
    cases hdec : decodeCalldata ["marketParams", "assets", "shares", "onBehalf", "receiver"]
        [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, abiAddress] I.calldata with
    | none => exact reEquivSelectorDecodingFailed hcode hr hd hdec
    | some args => exact reEquivSelectorRevert hcode hr hd hdec (bodyReverts_nonPayable hcv)
  have rd1 := morphoBlocks.morpho_block_7496_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd0
  have rdDecode := morphoBlocks.morpho_block_7503 (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  rcases morphoMarketTwoWordsTwoAddressesDecode (v := v) (R := [UInt256.ofNat 0, UInt256.ofNat 64])
      (by decide) hsz hsize (by rw [morphoPatchedValidJumps v]; jump_dest) rdDecode with
    ⟨hbad, hr⟩ | ⟨hb, a2, k2, C2, rd2⟩
  · have hdec : decodeCalldata ["marketParams", "assets", "shares", "onBehalf", "receiver"]
        [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, abiAddress] I.calldata = none := by
      rw [decodeCalldata_market_two_uint_two_address_eq, if_neg hbad]
    exact reEquivSelectorDecodingFailed hcode hr hd hdec
  · let p := marketParamsFromCalldata I.calldata
    let assets := calldataWord I.calldata 164
    let shares := calldataWord I.calldata 196
    let account := calldataWord I.calldata 228
    let receiver := calldataWord I.calldata 260
    let evm := initState σ σ₀ (.ofUInt256 g) A I
    have hdec : decodeCalldata ["marketParams", "assets", "shares", "onBehalf", "receiver"]
        [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, abiAddress] I.calldata =
        some (marketTransferArgs p assets shares account receiver) := by
      rw [decodeCalldata_market_two_uint_two_address_eq, if_pos hb]
      rfl
    have hbound : I.calldata.size < 2 ^ 255 + 4 := by have hh := hb.2.1; omega
    have hc : p.Canonical := hb.2.2.1
    have ha : account.toNat < EVM.addressModulus := hb.2.2.2.1
    have hr : receiver.toNat < EVM.addressModulus := hb.2.2.2.2
    rcases morphoWithdrawGuards p (R := []) (by decide) ha hr rd2 with
      ⟨hbad, hrev⟩ | ⟨hg, a3, k3, C3, rd3⟩
    · exact reEquivSelectorRevert hcode hrev hd hdec
        (morphoMarketTransferSourceReject (withdrawTransition.body.drop 11) p assets shares account receiver hc ha hr evm (immStore v) hcv hbound hbad)
    · have pref := morphoMarketTransferSourceGuards (withdrawTransition.body.drop 11) p assets shares account receiver hc ha hr evm (immStore v) hcv hbound hg
      have hl := marketTransferBeforeAccrue_locals p assets shares account receiver evm (immStore v)
      have ht := morphoWithdrawRefine p _ (immStore v) hc ha hr hl SourceState.init
        (by exact store_get_self _ _ _) rd3
      cases ht with
      | reverted he hr =>
        exact reEquivSelectorRevert hcode hr hd hdec (ExecFuncBody.execBlockRevert (pref.run he))
      | static he hr =>
        exact reEquivSelectorStatic hcode hr hd hdec (ExecFuncBody.execBlockStatic (pref.run he))
      | ok he hs' henc hr =>
        exact reEquivSelectorExecutionGen hcode hr hd hdec (ExecFuncBody.execBlockRet (pref.run he))
          hs'.accounts (.returned rfl henc)

end Benchmarks.Morpho.MorphoBlue
