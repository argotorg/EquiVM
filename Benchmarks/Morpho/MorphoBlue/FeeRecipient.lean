import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.BodyCommon
import Benchmarks.Morpho.MorphoBlue.Storage

/-!
# Morpho `feeRecipient()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9265; reach lemma `morphoReachFeeRecipientBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

theorem morphoFeeRecipientBodyReturns (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm ∅ feeRecipientTransition.body
      (.returned
        { contract := contract,
          locals := (∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata),
          immutables := immStore v }
        evm (some [.address (AccountAddress.ofNat
          (solcAddressSlotWord ⟨1⟩ evm.accountMap evm.executionEnv).toNat)]))
      (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (calldataPrelude_ok hcv hsize).returns
  exact evalMorphoAddress _ _ _ "feeRecipient" ⟨1⟩ (by simp) (by decide) (by rfl)

set_option maxRecDepth 10000 in
theorem morphoFeeRecipientXReturns {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 6))
    (hcv : I.weiValue = ⟨0⟩) (hbound : I.calldata.size < 2 ^ 255 + 4) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (solcAddressSlotWord ⟨1⟩ σ I).toByteArray := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 6) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachFeeRecipientBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have rdGuard := morphoBlocks.morpho_block_9265_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 0) hsz hbound hsize
  have rdReturn := morphoBlocks.morpho_block_9272_fallthrough (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have ret := morphoBlocks.morpho_block_9313 (immWords := wordsOf (immStore v)) (by decide) rdReturn
  exact (wordReturn_freePtr _) ▸ ret

set_option maxRecDepth 10000 in
theorem morphoFeeRecipientXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 6))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 6) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachFeeRecipientBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_9265_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond := solcCalldataStaticLenCheckHuge (words := 0) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_9272_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_9265_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

/-- `feeRecipient()`: the theorem `Correct.lean` routes selector 6 to. -/
theorem morphoFeeRecipientBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 6) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some feeRecipientTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (feeRecipientTransition.params.map Param.name)
      (transitionSignature feeRecipientTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldataWithMode_empty_ok hsz
  by_cases hcv : I.weiValue = ⟨0⟩
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · apply reEquivSelectorExecution hcode
        (morphoFeeRecipientXReturns v hcode hsize hsel hcv hbound) hd hdec
        (morphoFeeRecipientBodyReturns v _ hcv hbound)
      exact .returned rfl (solcAddressReturnEncoding rfl _)
    · exact reEquivSelectorRevert hcode
        (morphoFeeRecipientXReverts v hcode hsize hsel (.inr (by omega))) hd hdec
        (calldataPrelude_reverts hcv hbound)
  · exact reEquivSelectorRevert hcode
      (morphoFeeRecipientXReverts v hcode hsize hsel (.inl hcv)) hd hdec
      (bodyReverts_nonPayable hcv)

end Benchmarks.Morpho.MorphoBlue
