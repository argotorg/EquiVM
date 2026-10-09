import Benchmarks.Morpho.MorphoBlue.SupplyRefine
import Benchmarks.Morpho.MorphoBlue.MarketTwoWordsAddressBytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

/-- `supply((address,address,address,address,uint256),uint256,uint256,address,bytes)`: the theorem `Correct.lean` routes selector 19 to. -/
theorem morphoSupplyBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 19)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 19) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some supplyTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  obtain ⟨k0, C0, rd0⟩ := morphoReachSupplyBody (g := .ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd0
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := morphoBlocks.morpho_block_3802_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd1
    cases hdec : decodeCalldata ["marketParams", "assets", "shares", "onBehalf", "data"]
        [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, .bytes] I.calldata with
    | none => exact reEquivSelectorDecodingFailed hcode hr hd hdec
    | some args => exact reEquivSelectorRevert hcode hr hd hdec (bodyReverts_nonPayable hcv)
  have rd1 := morphoBlocks.morpho_block_3802_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd0
  have rdDecode := morphoBlocks.morpho_block_3809 (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  rcases morphoMarketTwoWordsAddressBytesDecode (v := v) (R := [UInt256.ofNat 0])
      (by decide) hsz hsize (by rw [morphoPatchedValidJumps v]; jump_dest) rdDecode with
    ⟨hbad, hr⟩ | ⟨hb, a2, k2, C2, rd2⟩
  · have hdec : decodeCalldata ["marketParams", "assets", "shares", "onBehalf", "data"]
        [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, .bytes] I.calldata = none := by
      rw [decodeCalldata_market_two_uint_address_bytes_eq, if_neg hbad]
    exact reEquivSelectorDecodingFailed hcode hr hd hdec
  · let p := marketParamsFromCalldata I.calldata
    let assets := calldataWord I.calldata 164
    let shares := calldataWord I.calldata 196
    let account := calldataWord I.calldata 228
    let data := calldataBytesPayload I.calldata (4 + (calldataWord I.calldata 260).toNat)
    let evm := initState σ σ₀ (.ofUInt256 g) A I
    have hdec : decodeCalldata ["marketParams", "assets", "shares", "onBehalf", "data"]
        [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, .bytes] I.calldata =
        some (supplyArgs p assets shares account data) := by
      rw [decodeCalldata_market_two_uint_address_bytes_eq, if_pos hb]
      rfl
    have hbound : I.calldata.size < 2 ^ 255 + 4 := by have hh := hb.2.1; omega
    have hc : p.Canonical := hb.2.2.1
    have ha : account.toNat < EVM.addressModulus := hb.2.2.2.1
    rcases morphoSupplyGuards p (R := []) (by decide) ha rd2 with
      ⟨hbad, hr⟩ | ⟨hg, a3, k3, C3, rd3⟩
    · exact reEquivSelectorRevert hcode hr hd hdec
        (morphoSupplySourceReject p assets shares account data hc ha evm (immStore v) hcv hbound hbad)
    · have pref := morphoSupplySourceGuards p assets shares account data hc ha evm (immStore v) hcv hbound hg
      have hl := supplyBeforeAccrue_locals p assets shares account data evm (immStore v)
      have hstart : (UInt256.ofNat 4 + calldataWord I.calldata 260).toNat =
          4 + (calldataWord I.calldata 260).toNat := add4_word_toNat _ hb.2.2.2.2.1
      have hoff : ((UInt256.ofNat 4 + calldataWord I.calldata 260) + UInt256.ofNat 32).toNat =
          4 + (calldataWord I.calldata 260).toNat + 32 := by
        have hh := hb.2.2.2.2.1
        have hfit : (UInt256.ofNat 4 + calldataWord I.calldata 260).toNat + 32 < UInt256.size := by
          rw [hstart]; norm_num [solcMaxU64, UInt256.size] at hh ⊢; omega
        rw [uadd_word_ofNat_toNat _ 32 hfit, hstart]
      have hbytes := hb.2.2.2.2.2
      have ht := morphoSupplyRefine p _ (immStore v) hc ha hl SourceState.init
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
