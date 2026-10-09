import Benchmarks.Morpho.MorphoBlue.FlashLoanCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

/-- The public flash-loan path, including all three external-call outcomes. -/
theorem morphoFlashLoanBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 22)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 22) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some flashLoanTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  obtain ⟨k0, C0, rd0⟩ := morphoReachFlashLoanBody (g := .ofUInt256 g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd0
  by_cases hcv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := morphoBlocks.morpho_block_920_taken (immWords := wordsOf (immStore v))
      (by decide) hcv (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    have hr := morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rd1
    cases hdec : decodeCalldata ["token", "assets", "data"] [abiAddress, abiUInt256, .bytes] I.calldata with
    | none => exact reEquivSelectorDecodingFailed hcode hr hd hdec
    | some args => exact reEquivSelectorRevert hcode hr hd hdec (bodyReverts_nonPayable hcv)
  have rd1 := morphoBlocks.morpho_block_920_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd0
  rcases morphoFlashLoanDecode (v := v) (R := []) (by decide) hsz hsize rd1 with
    ⟨hbad, hr⟩ | ⟨hb, k2, C2, rd2⟩
  · have hdec : decodeCalldata ["token", "assets", "data"] [abiAddress, abiUInt256, .bytes] I.calldata = none := by
      rw [decodeCalldata_address_uint256_bytes_eq, if_neg hbad]
    exact reEquivSelectorDecodingFailed hcode hr hd hdec
  · let token := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
    let assets := calldataWord I.calldata 36
    let data := calldataBytesPayload I.calldata (4 + (calldataWord I.calldata 68).toNat)
    let evm := initState σ σ₀ (.ofUInt256 g) A I
    have hdec : decodeCalldata ["token", "assets", "data"] [abiAddress, abiUInt256, .bytes] I.calldata =
        some (flashLoanArgs token assets data) := by
      rw [decodeCalldata_address_uint256_bytes_eq, if_pos hb]
      rfl
    have hbound : I.calldata.size < 2 ^ 255 + 4 := by have hh := hb.2.1; omega
    by_cases hz : assets = ⟨0⟩
    · exact reEquivSelectorRevert hcode (morphoFlashLoanGuardZero (by decide) hz rd2) hd hdec
        (morphoFlashLoanSourceZero token assets data evm (immStore v) hcv hbound hz)
    · obtain ⟨a3, k3, C3, rd3⟩ := morphoFlashLoanGuardOk (by decide) hz rd2
      by_cases hp : I.perm = true
      swap
      · have hp' : I.perm = false := Bool.eq_false_iff.mpr hp
        exact reEquivSelectorStatic hcode (morphoFlashLoanEventStatic (by simp [flashLoanGuardStack]) hp' rd3)
          hd hdec (morphoFlashLoanSourceStatic token assets data evm (immStore v) hcv hbound hz hp')
      · obtain ⟨a4, k4, C4, rd4⟩ := morphoFlashLoanEnter (by decide) hb.2.2.1 hp rd3
        have htoken : UInt256.ofNat token.val = calldataWord I.calldata 4 :=
          addressWord_eq_ofNat_address hb.2.2.1
        have hstart : (UInt256.ofNat 4 + calldataWord I.calldata 68).toNat =
            4 + (calldataWord I.calldata 68).toNat := add4_word_toNat _ hb.2.2.2.1
        have hoff : ((UInt256.ofNat 4 + calldataWord I.calldata 68) + UInt256.ofNat 32).toNat =
            4 + (calldataWord I.calldata 68).toNat + 32 := by
          have hh := hb.2.2.2.1
          have hhfit : (UInt256.ofNat 4 + calldataWord I.calldata 68).toNat + 32 < UInt256.size := by
            rw [hstart]
            norm_num [solcMaxU64, UInt256.size] at hh ⊢
            omega
          rw [uadd_word_ofNat_toNat _ 32 hhfit, hstart]
        have hbytes := hb.2.2.2.2
        have hread := calldataBytesPayload_read hbytes
        have hdataSize := calldataBytesPayload_size hbytes
        have hi := flashLoanFrame_inputs token assets data I.calldata (immStore v)
        have pref := morphoFlashLoanSourceEnter token assets data evm (immStore v) hcv hbound hz
        have hr : RD (deployedRuntime v) I (.ofUInt256 g) evm (UInt256.ofNat 14666)
            [UInt256.ofNat token.val, UInt256.ofNat I.source.val, assets, UInt256.ofNat 1113,
              (UInt256.ofNat 4 + calldataWord I.calldata 68) + UInt256.ofNat 32,
              calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat), UInt256.ofNat 0,
              assets, UInt256.ofNat token.val, UInt256.ofNat 0]
            (flashLoanEnterMem assets) a4 ByteArray.empty σ k4 C4 := by
          rw [htoken]
          exact rd4
        have hf := morphoFlashLoanCalls token _ (immStore v) hi SourceState.init hbytes.2.1
          (by rw [hoff]; exact hbytes.2.2) (by rw [hoff]; exact hread) hdataSize hr
        cases hf with
        | reverted he hx =>
          exact reEquivSelectorRevert hcode hx hd hdec (ExecFuncBody.execBlockRevert (pref.run he))
        | ok he hs' hx =>
          exact reEquivSelectorExecutionGen hcode hx hd hdec (ExecFuncBody.execBlockOK (pref.run he))
            hs'.accounts (.fallthrough rfl rfl (by native_decide))

end Benchmarks.Morpho.MorphoBlue
