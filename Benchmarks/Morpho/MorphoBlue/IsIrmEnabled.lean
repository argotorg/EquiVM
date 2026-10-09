import Benchmarks.Morpho.MorphoBlue.Routines
import Benchmarks.Morpho.MorphoBlue.Storage

/-!
# Morpho `isIrmEnabled(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 337; reach lemma `morphoReachIsIrmEnabledBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

def isIrmEnabledArgs (cd : ByteArray) : Store :=
  (∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))

theorem morphoIsIrmEnabledBodyReturns (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (isIrmEnabledArgs evm.executionEnv.calldata)
      isIrmEnabledTransition.body
      (.returned
        { contract := contract,
          locals := (isIrmEnabledArgs evm.executionEnv.calldata).insert "__calldata"
            (.bytes evm.executionEnv.calldata), immutables := immStore v }
        evm (some [wordToElem .bool (UInt256.land
          (solcSlotWordAt (solcMappingSlot ⟨4⟩ (calldataWord evm.executionEnv.calldata 4))
            evm.accountMap evm.executionEnv) ⟨255⟩)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (calldataPrelude_ok hcv hsize).returns
  apply evalMorphoIrmEnabled
  · simp [isIrmEnabledArgs]
  · simp only [evalExpr?, isIrmEnabledArgs,
      store_get_ne (k := "__calldata") (a := "arg0") _ _ (by decide),
      store_get_self, EvalResult.ofOption]
  · exact hcanon

set_option maxRecDepth 10000 in
theorem morphoIsIrmEnabledReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 26))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11354)
      [UInt256.ofNat 420, solcAddrMask, ⟨0⟩, ⟨64⟩, ⟨255⟩, ⟨32⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachIsIrmEnabledBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  have rdGuard := morphoBlocks.morpho_block_337_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 1) hlen hbound hsize
  have rdCall := morphoBlocks.morpho_block_343_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have rdDecode := morphoBlocks.morpho_block_385
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCall
  exact ⟨_, _, rdDecode⟩

set_option maxRecDepth 10000 in
theorem morphoIsIrmEnabledXReturns {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 26))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (UInt256.land
        (solcSlotWordAt (solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4)) σ I) ⟨255⟩))).toByteArray := by
  obtain ⟨k, C, rd⟩ := morphoIsIrmEnabledReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound
  obtain ⟨k', C', rdReturn⟩ := morphoDecodeAddress4Ok (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hcanon rd
  have ret := morphoBlocks.morpho_block_420
    (immWords := wordsOf (immStore v)) (by decide) rdReturn
  change RDret _ _ _ _
    (let mem := twoWordHashMem (UInt256.land (calldataWord I.calldata 4) solcAddrMask)
       ⟨4⟩ solcFreePtrMem
     ((UInt256.isZero (UInt256.isZero (UInt256.land
       (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ mem) σ I) ⟨255⟩))).toByteArray.write 0 mem
       (memLoad ⟨64⟩ mem).toNat 32).readWithPadding (memLoad ⟨64⟩ mem).toNat 32) at ret
  rw [solcAddrMask_clean hcanon] at ret
  dsimp only at ret
  rw [show keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (calldataWord I.calldata 4) ⟨4⟩ solcFreePtrMem) =
    solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4) from
    twoWordHashMem_solcMappingSlot_any _ _ _] at ret
  exact (wordReturn_twoWordHash _ _ _) ▸ ret

set_option maxRecDepth 10000 in
theorem morphoIsIrmEnabledXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 26))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 26) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachIsIrmEnabledBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_337_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 32) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 1) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 1) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_343_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_337_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

set_option maxRecDepth 10000 in
theorem morphoIsIrmEnabledXNoncanonical {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 26)) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases hcv : I.weiValue = ⟨0⟩
  · obtain ⟨k, C, rd⟩ := morphoIsIrmEnabledReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound
    exact morphoDecodeAddress4Revert (by decide) hnc rd
  · exact morphoIsIrmEnabledXReverts v hcode hsize hsel (.inl hcv)

/-- `isIrmEnabled(address)`: the theorem `Correct.lean` routes selector 26 to. -/
theorem morphoIsIrmEnabledBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 26)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 26) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some isIrmEnabledTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (isIrmEnabledTransition.params.map Param.name)
            (transitionSignature isIrmEnabledTransition).paramTypes I.calldata =
            some (isIrmEnabledArgs I.calldata) := decodeCalldata_address_ok hlen hbound hcanon
        by_cases hcv : I.weiValue = ⟨0⟩
        · apply reEquivSelectorExecution hcode
            (morphoIsIrmEnabledXReturns v hcode hsize hsel hcv hlen hbound hcanon) hd hdec
            (morphoIsIrmEnabledBodyReturns v _ hcv hbound hcanon)
          exact .returned rfl (boolWordReturnEncoding _)
        · exact reEquivSelectorRevert hcode
            (morphoIsIrmEnabledXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · exact reEquivSelectorDecodingFailed hcode
          (morphoIsIrmEnabledXNoncanonical v hcode hsize hsel hlen hbound hcanon) hd
          (decodeCalldata_address_none_noncanon hlen hbound hcanon)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoIsIrmEnabledXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_address_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoIsIrmEnabledXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_address_none_short hsz (by omega))

end Benchmarks.Morpho.MorphoBlue
