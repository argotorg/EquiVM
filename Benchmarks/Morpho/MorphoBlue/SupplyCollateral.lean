import Benchmarks.Morpho.MorphoBlue.SupplyCollateralTail
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

/-- `supplyCollateral((address,address,address,address,uint256),uint256,address,bytes)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem morphoSupplyCollateralBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 3) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some supplyCollateralTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  obtain ⟨k0, C0, rd0⟩ := morphoReachSupplyCollateralBody (g := .ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd0
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := morphoBlocks.morpho_block_9975_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd1
    cases hdec : decodeCalldata ["marketParams", "assets", "onBehalf", "data"]
        [marketParamsABIType, abiUInt256, abiAddress, .bytes] I.calldata with
    | none => exact reEquivSelectorDecodingFailed hcode hr hd hdec
    | some args => exact reEquivSelectorRevert hcode hr hd hdec (bodyReverts_nonPayable hcv)
  have rd1 := morphoBlocks.morpho_block_9975_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd0
  rcases morphoSupplyCollateralDecode (v := v) (R := []) (by decide) hsz hsize rd1 with
    ⟨hbad, hr⟩ | ⟨hb, a2, k2, C2, rd2⟩
  · have hdec : decodeCalldata ["marketParams", "assets", "onBehalf", "data"]
        [marketParamsABIType, abiUInt256, abiAddress, .bytes] I.calldata = none := by
      rw [decodeCalldata_market_uint_address_bytes_eq, if_neg hbad]
    exact reEquivSelectorDecodingFailed hcode hr hd hdec
  · let p := marketParamsFromCalldata I.calldata
    let assets := calldataWord I.calldata 164
    let account := calldataWord I.calldata 196
    let data := calldataBytesPayload I.calldata (4 + (calldataWord I.calldata 228).toNat)
    let evm := initState σ σ₀ (.ofUInt256 g) A I
    have hdec : decodeCalldata ["marketParams", "assets", "onBehalf", "data"]
        [marketParamsABIType, abiUInt256, abiAddress, .bytes] I.calldata =
        some (supplyCollateralArgs p assets account data) := by
      rw [decodeCalldata_market_uint_address_bytes_eq, if_pos hb]
      rfl
    have hbound : I.calldata.size < 2 ^ 255 + 4 := by have hh := hb.2.1; omega
    have hc : p.Canonical := hb.2.2.1
    have ha : account.toNat < EVM.addressModulus := hb.2.2.2.1
    rcases morphoSupplyCollateralGuards p (R := []) (by decide) ha rd2 with
      ⟨hbad, hr⟩ | ⟨hg, a3, k3, C3, rd3⟩
    · exact reEquivSelectorRevert hcode hr hd hdec
        (morphoSupplyCollateralSourceReject p assets account data hc ha evm (immStore v) hcv hbound hbad)
    · have pref := morphoSupplyCollateralSourceGuards p assets account data hc ha evm (immStore v) hcv hbound hg
      have hl := supplyCollateralFrame_locals p assets account data I.calldata (immStore v)
      have hf := morphoSupplyCollateralUpdateRefine p data _ (immStore v) (by decide) ha hl SourceState.init rd3
      cases hf with
      | reverted he hr =>
        exact reEquivSelectorRevert hcode hr hd hdec (ExecFuncBody.execBlockRevert (pref.run he))
      | static he hr =>
        exact reEquivSelectorStatic hcode hr hd hdec (ExecFuncBody.execBlockStatic (pref.run he))
      | @ok evm' σ' a4 out4 k4 C4 hab hs' hp rd4 =>
        have hl1 := hl.insert "__c1" (.int (Int.ofNat assets.toNat)) (by decide) (by decide)
        have hstart : (UInt256.ofNat 4 + calldataWord I.calldata 228).toNat =
            4 + (calldataWord I.calldata 228).toNat := add4_word_toNat _ hb.2.2.2.2.1
        have hoff : ((UInt256.ofNat 4 + calldataWord I.calldata 228) + UInt256.ofNat 32).toNat =
            4 + (calldataWord I.calldata 228).toNat + 32 := by
          have hh := hb.2.2.2.2.1
          have hfit : (UInt256.ofNat 4 + calldataWord I.calldata 228).toNat + 32 < UInt256.size := by
            rw [hstart]; norm_num [solcMaxU64, UInt256.size] at hh ⊢; omega
          rw [uadd_word_ofNat_toNat _ 32 hfit, hstart]
        have hbytes := hb.2.2.2.2.2
        have ht := morphoSupplyCollateralTail p _ (immStore v) hc hl1 hs' hp hbytes.2.1
          (by rw [hoff]; exact hbytes.2.2) (by rw [hoff]; exact calldataBytesPayload_read hbytes)
          (calldataBytesPayload_size hbytes) rd4
        cases ht with
        | reverted he hr =>
          exact reEquivSelectorRevert hcode hr hd hdec (ExecFuncBody.execBlockRevert (pref.run (hab.run he)))
        | static he hr =>
          exact reEquivSelectorStatic hcode hr hd hdec (ExecFuncBody.execBlockStatic (pref.run (hab.run he)))
        | ok he hs'' hr =>
          exact reEquivSelectorExecutionGen hcode hr hd hdec (ExecFuncBody.execBlockOK (pref.run (hab.run he)))
            hs''.accounts (.fallthrough rfl rfl (by native_decide))

end Benchmarks.Morpho.MorphoBlue
