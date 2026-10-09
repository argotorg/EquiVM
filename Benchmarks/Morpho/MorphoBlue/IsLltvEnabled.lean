import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.BodyCommon
import Benchmarks.Morpho.MorphoBlue.Storage

/-!
# Morpho `isLltvEnabled(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3725; reach lemma `morphoReachIsLltvEnabledBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

def isLltvEnabledArgs (cd : ByteArray) : Store :=
  (∅ : Store).insert "arg0" (.int (Int.ofNat (calldataWord cd 4).toNat))

theorem morphoIsLltvEnabledBodyReturns (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm (isLltvEnabledArgs evm.executionEnv.calldata)
      isLltvEnabledTransition.body
      (.returned
        { contract := contract,
          locals := (isLltvEnabledArgs evm.executionEnv.calldata).insert "__calldata"
            (.bytes evm.executionEnv.calldata), immutables := immStore v }
        evm (some [wordToElem .bool (UInt256.land
          (solcSlotWordAt (solcMappingSlot ⟨5⟩ (calldataWord evm.executionEnv.calldata 4))
            evm.accountMap evm.executionEnv) ⟨255⟩)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (calldataPrelude_ok hcv hsize).returns
  apply evalMorphoLltvEnabled
  · simp [isLltvEnabledArgs]
  · simp only [evalExpr?, isLltvEnabledArgs,
      store_get_ne (k := "__calldata") (a := "arg0") _ _ (by decide),
      store_get_self, EvalResult.ofOption]

set_option maxRecDepth 10000 in
theorem morphoIsLltvEnabledXReturns {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 20))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (UInt256.land
        (solcSlotWordAt (solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4)) σ I) ⟨255⟩))).toByteArray := by
  have hsz : 4 ≤ I.calldata.size := by omega
  obtain ⟨k, C, rd⟩ := morphoReachIsLltvEnabledBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have rdGuard := morphoBlocks.morpho_block_3725_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 1) hlen hbound hsize
  have rdReturn := morphoBlocks.morpho_block_3732_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have ret := morphoBlocks.morpho_block_3774
    (immWords := wordsOf (immStore v)) (by decide) rdReturn
  change RDret _ _ _ _
    (let mem := twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ solcFreePtrMem
     ((UInt256.isZero (UInt256.isZero (UInt256.land
       (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ mem) σ I) ⟨255⟩))).toByteArray.write 0 mem
       (memLoad ⟨64⟩ mem).toNat 32).readWithPadding (memLoad ⟨64⟩ mem).toNat 32) at ret
  dsimp only at ret
  rw [show keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (calldataWord I.calldata 4) ⟨5⟩ solcFreePtrMem) =
    solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4) from
    twoWordHashMem_solcMappingSlot_any _ _ _] at ret
  exact (wordReturn_twoWordHash _ _ _) ▸ ret

set_option maxRecDepth 10000 in
theorem morphoIsLltvEnabledXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 20))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 20) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachIsLltvEnabledBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_3725_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 32) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 1) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 1) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_3732_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_3725_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

/-- `isLltvEnabled(uint256)`: the theorem `Correct.lean` routes selector 20 to. -/
theorem morphoIsLltvEnabledBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 20)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hd : selectorDispatchMsg contract I.calldata = some isLltvEnabledTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · have hdec : decodeCalldataWithMode config.abiDecodeMode
          (isLltvEnabledTransition.params.map Param.name)
          (transitionSignature isLltvEnabledTransition).paramTypes I.calldata =
          some (isLltvEnabledArgs I.calldata) := decodeCalldata_uint256_ok hlen hbound
      by_cases hcv : I.weiValue = ⟨0⟩
      · apply reEquivSelectorExecution hcode
          (morphoIsLltvEnabledXReturns v hcode hsize hsel hcv hlen hbound) hd hdec
          (morphoIsLltvEnabledBodyReturns v _ hcv hbound)
        exact .returned rfl (boolWordReturnEncoding _)
      · exact reEquivSelectorRevert hcode
          (morphoIsLltvEnabledXReverts v hcode hsize hsel (.inl hcv)) hd hdec
          (bodyReverts_nonPayable hcv)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoIsLltvEnabledXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_uint256_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoIsLltvEnabledXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_uint256_none_short (by omega))

end Benchmarks.Morpho.MorphoBlue
