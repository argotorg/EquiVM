import Benchmarks.Morpho.MorphoBlue.Routines
import Benchmarks.Morpho.MorphoBlue.Storage

/-!
# Morpho `isAuthorized(address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7223; reach lemma `morphoReachIsAuthorizedBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

def isAuthorizedArgs (cd : ByteArray) : Store :=
  ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert
    "arg1" (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))

theorem morphoIsAuthorizedBodyReturns (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord evm.executionEnv.calldata 36).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (isAuthorizedArgs evm.executionEnv.calldata)
      isAuthorizedTransition.body
      (.returned
        { contract := contract,
          locals := (isAuthorizedArgs evm.executionEnv.calldata).insert "__calldata"
            (.bytes evm.executionEnv.calldata), immutables := immStore v }
        evm (some [wordToElem .bool (UInt256.land
          (solcSlotWordAt (authorizationSlot (calldataWord evm.executionEnv.calldata 4)
            (calldataWord evm.executionEnv.calldata 36)) evm.accountMap evm.executionEnv)
          ⟨255⟩)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (calldataPrelude_ok hcv hsize).returns
  apply evalMorphoIsAuthorized
  · simp [isAuthorizedArgs]
  · simp only [evalExpr?, isAuthorizedArgs,
      store_get_ne (k := "__calldata") (a := "arg0") _ _ (by decide),
      store_get_ne (k := "arg1") (a := "arg0") _ _ (by decide),
      store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, isAuthorizedArgs,
      store_get_ne (k := "__calldata") (a := "arg1") _ _ (by decide),
      store_get_self, EvalResult.ofOption]
  · exact hcanon0
  · exact hcanon1

set_option maxRecDepth 10000 in
theorem morphoIsAuthorizedReachDecode0 {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 11))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11354)
      [UInt256.ofNat 7279, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachIsAuthorizedBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  have rdGuard := morphoBlocks.morpho_block_7223_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 2) hlen hbound hsize
  have rdCall := morphoBlocks.morpho_block_7230_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have rdDecode := morphoBlocks.morpho_block_7272
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCall
  exact ⟨_, _, rdDecode⟩

set_option maxRecDepth 10000 in
theorem morphoIsAuthorizedReachDecode1 {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 11))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11424)
      [UInt256.ofNat 7289, ⟨64⟩, calldataWord I.calldata 4, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoIsAuthorizedReachDecode0 (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound
  obtain ⟨k', C', rdCall⟩ := morphoDecodeAddress4Ok (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hcanon0 rd
  have rdDecode := morphoBlocks.morpho_block_7279
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCall
  exact ⟨_, _, rdDecode⟩

set_option maxRecDepth 10000 in
theorem morphoIsAuthorizedXReturns {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 11))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (UInt256.land
        (solcSlotWordAt (authorizationSlot (calldataWord I.calldata 4)
          (calldataWord I.calldata 36)) σ I) ⟨255⟩))).toByteArray := by
  obtain ⟨k, C, rd⟩ := morphoIsAuthorizedReachDecode1 (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon0
  obtain ⟨k', C', rdReturn⟩ := morphoDecodeAddress36Ok (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hcanon1 rd
  have ret := morphoBlocks.morpho_block_7289
    (immWords := wordsOf (immStore v)) (by decide) rdReturn
  change RDret _ _ _ _
    (let mem0 := twoWordHashMem (UInt256.land (calldataWord I.calldata 4) solcAddrMask)
       ⟨6⟩ solcFreePtrMem
     let mem := twoWordHashMem (UInt256.land (calldataWord I.calldata 36) solcAddrMask)
       (keccakWord ⟨0⟩ ⟨64⟩ mem0) mem0
     ((UInt256.isZero (UInt256.isZero (UInt256.land
       (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ mem) σ I) ⟨255⟩))).toByteArray.write 0 mem
       (memLoad ⟨64⟩ mem).toNat 32).readWithPadding (memLoad ⟨64⟩ mem).toNat 32) at ret
  rw [solcAddrMask_clean hcanon0, solcAddrMask_clean hcanon1] at ret
  dsimp only at ret
  have hslot0 : keccakWord ⟨0⟩ ⟨64⟩
      (twoWordHashMem (calldataWord I.calldata 4) ⟨6⟩ solcFreePtrMem) =
      solcMappingSlot ⟨6⟩ (calldataWord I.calldata 4) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hslot0] at ret
  have hmem : twoWordHashMem (calldataWord I.calldata 36)
      (solcMappingSlot ⟨6⟩ (calldataWord I.calldata 4))
      (twoWordHashMem (calldataWord I.calldata 4) ⟨6⟩ solcFreePtrMem) =
      twoWordHashMem (calldataWord I.calldata 36)
        (solcMappingSlot ⟨6⟩ (calldataWord I.calldata 4)) solcFreePtrMem :=
    twoWordHashMem_eq_of_size_read64_128 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size) solcFreePtrMem_size
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
      solcFreePtrMem_read64
  rw [hmem] at ret
  have hslot1 : keccakWord ⟨0⟩ ⟨64⟩
      (twoWordHashMem (calldataWord I.calldata 36)
        (solcMappingSlot ⟨6⟩ (calldataWord I.calldata 4)) solcFreePtrMem) =
      authorizationSlot (calldataWord I.calldata 4) (calldataWord I.calldata 36) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hslot1] at ret
  exact (wordReturn_twoWordHash _ _ _) ▸ ret

set_option maxRecDepth 10000 in
theorem morphoIsAuthorizedXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 11))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 11) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachIsAuthorizedBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_7223_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 64) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 2) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 2) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_7230_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_7223_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

set_option maxRecDepth 10000 in
theorem morphoIsAuthorizedXNoncanonical {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 11)) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ ((calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 36).toNat < EVM.addressModulus)) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases hcv : I.weiValue = ⟨0⟩
  · by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
    · obtain ⟨k, C, rd⟩ := morphoIsAuthorizedReachDecode1 (g := g) (σ := σ) (σ₀ := σ₀)
        (A := A) v hcode hsize hsel hcv hlen hbound hc0
      exact morphoDecodeAddress36Revert (by simp) (fun hc1 => hnc ⟨hc0, hc1⟩) rd
    · obtain ⟨k, C, rd⟩ := morphoIsAuthorizedReachDecode0 (g := g) (σ := σ) (σ₀ := σ₀)
        (A := A) v hcode hsize hsel hcv hlen hbound
      exact morphoDecodeAddress4Revert (by decide) hc0 rd
  · exact morphoIsAuthorizedXReverts v hcode hsize hsel (.inl hcv)

/-- `isAuthorized(address,address)`: the theorem `Correct.lean` routes selector 11 to. -/
theorem morphoIsAuthorizedBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 11)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 11) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some isAuthorizedTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 68 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
          (calldataWord I.calldata 36).toNat < EVM.addressModulus
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (isAuthorizedTransition.params.map Param.name)
            (transitionSignature isAuthorizedTransition).paramTypes I.calldata =
            some (isAuthorizedArgs I.calldata) :=
          decodeCalldata_address_address_ok hlen hbound hcanon.1 hcanon.2
        by_cases hcv : I.weiValue = ⟨0⟩
        · apply reEquivSelectorExecution hcode
            (morphoIsAuthorizedXReturns v hcode hsize hsel hcv hlen hbound hcanon.1 hcanon.2)
            hd hdec (morphoIsAuthorizedBodyReturns v _ hcv hbound hcanon.1 hcanon.2)
          exact .returned rfl (boolWordReturnEncoding _)
        · exact reEquivSelectorRevert hcode
            (morphoIsAuthorizedXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · apply reEquivSelectorDecodingFailed hcode
          (morphoIsAuthorizedXNoncanonical v hcode hsize hsel hlen hbound hcanon) hd
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · exact decodeCalldata_address_address_none_noncanon1 hlen hbound hc0
            (fun hc1 => hcanon ⟨hc0, hc1⟩)
        · exact decodeCalldata_address_address_none_noncanon0 hlen hbound hc0
    · exact reEquivSelectorDecodingFailed hcode
        (morphoIsAuthorizedXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_address_address_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoIsAuthorizedXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_address_address_none_short hsz (by omega))

end Benchmarks.Morpho.MorphoBlue
