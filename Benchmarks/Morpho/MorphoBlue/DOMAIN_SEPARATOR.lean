import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.BodyCommon

/-!
# Morpho `DOMAIN_SEPARATOR()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9347; reach lemma `morphoReachDOMAIN_SEPARATORBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

theorem morphoDOMAIN_SEPARATORBodyReturns (v : MorphoImmutables) (evm : EVM.State) (locals : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm locals dOMAIN_SEPARATORTransition.body
      (.returned
        { contract := contract,
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata),
          immutables := immStore v }
        evm (some [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE v.DOMAIN_SEPARATOR)]))
      (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (calldataPrelude_ok hcv hsize).returns (evalImmutable_DOMAIN_SEPARATOR _ _ _ _ _)


set_option maxRecDepth 10000 in
theorem morphoDOMAIN_SEPARATORXReturns {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 5))
    (hcv : I.weiValue = ⟨0⟩) (hbound : I.calldata.size < 2 ^ 255 + 4) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      v.DOMAIN_SEPARATOR.toByteArray := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 5) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachDOMAIN_SEPARATORBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have rdGuard := morphoBlocks.morpho_block_9347_fallthrough (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 0) hsz hbound hsize
  have rdReturn := morphoBlocks.morpho_block_9354_fallthrough (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have ret := morphoBlocks.morpho_block_9395 (immWords := wordsOf (immStore v)) (by decide) rdReturn
  rw [wordsOf_immStore_DOMAIN_SEPARATOR] at ret
  exact (wordReturn_freePtr _) ▸ ret

set_option maxRecDepth 10000 in
theorem morphoDOMAIN_SEPARATORXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 5))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 5) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachDOMAIN_SEPARATORBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_9347_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond := solcCalldataStaticLenCheckHuge (words := 0) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_9354_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_9347_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

/-- `DOMAIN_SEPARATOR()`: the theorem `Correct.lean` routes selector 5 to. -/
theorem morphoDOMAIN_SEPARATORBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 5) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some dOMAIN_SEPARATORTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (dOMAIN_SEPARATORTransition.params.map Param.name)
      (transitionSignature dOMAIN_SEPARATORTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldataWithMode_empty_ok hsz
  by_cases hcv : I.weiValue = ⟨0⟩
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · apply reEquivSelectorExecution hcode
        (morphoDOMAIN_SEPARATORXReturns v hcode hsize hsel hcv hbound) hd hdec
        (morphoDOMAIN_SEPARATORBodyReturns v _ ∅ hcv hbound)
      exact .returned rfl (bytes32ReturnEncoding _)
    · exact reEquivSelectorRevert hcode
        (morphoDOMAIN_SEPARATORXReverts v hcode hsize hsel (.inr (by omega))) hd hdec
        (calldataPrelude_reverts hcv hbound)
  · exact reEquivSelectorRevert hcode
      (morphoDOMAIN_SEPARATORXReverts v hcode hsize hsel (.inl hcv)) hd hdec
      (bodyReverts_nonPayable hcv)

end Benchmarks.Morpho.MorphoBlue
