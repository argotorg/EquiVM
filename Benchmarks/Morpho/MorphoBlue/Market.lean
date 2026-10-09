import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.ReturnCommon
import Benchmarks.Morpho.MorphoBlue.MarketStateCommon

/-!
# Morpho `market(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7351; reach lemma `morphoReachMarketBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

def marketArgs (cd : ByteArray) : Store :=
  (∅ : Store).insert "arg0" (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (calldataWord cd 4)))

theorem morphoMarketBodyReturns (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm (marketArgs evm.executionEnv.calldata)
      marketTransition.body
      (.returned
        { contract := contract,
          locals := (marketArgs evm.executionEnv.calldata).insert "__calldata"
            (.bytes evm.executionEnv.calldata), immutables := immStore v }
        evm (some ((marketReturnEntries evm.accountMap evm.executionEnv
          (calldataWord evm.executionEnv.calldata 4)).map (fun e => e.2.1)))) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (calldataPrelude_ok hcv hsize).run
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hbase : ((marketArgs evm.executionEnv.calldata).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).get? "market" = none := by
    simp [marketArgs]
  have hkey : evalExpr? config
      { contract := contract,
        locals := (marketArgs evm.executionEnv.calldata).insert "__calldata"
          (.bytes evm.executionEnv.calldata), immutables := immStore v }
      evm (.var "arg0") =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (calldataWord evm.executionEnv.calldata 4))) := by
    simp only [evalExpr?, marketArgs,
      store_get_ne (k := "__calldata") (a := "arg0") _ _ (by decide),
      store_get_self, EvalResult.ofOption]
  have he (i : Fin 6) := evalMorphoMarketField evm _ (immStore v) (.var "arg0")
    (calldataWord evm.executionEnv.calldata 4) i hbase hkey
  have h0 := he ⟨0, by decide⟩
  have h1 := he ⟨1, by decide⟩
  have h2 := he ⟨2, by decide⟩
  have h3 := he ⟨3, by decide⟩
  have h4 := he ⟨4, by decide⟩
  have h5 := he ⟨5, by decide⟩
  simp only [marketFieldName] at h0 h1 h2 h3 h4 h5
  simp only [evalExprs?, marketReturnEntries, List.map_cons, List.map_nil,
    h0, h1, h2, h3, h4, h5, pure, bind, EvalResult.bind]

theorem morphoMarketReturnEncoding (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    encodeReturnValues? marketTransition.returnType
      ((marketReturnEntries σ I id).map (fun e => e.2.1)) =
      some (returnWordBytes ((marketReturnEntries σ I id).map (fun e => e.2.2))) := by
  apply elementaryWordsReturnEncoding (marketReturnEntries σ I id)
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  exact encodeABIValue_uint _ _ (halfWord_bound _ _)

set_option maxRecDepth 10000 in
theorem morphoMarketXReturns {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 23))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (returnWordBytes ((marketReturnEntries σ I (calldataWord I.calldata 4)).map
        (fun e => e.2.2))) := by
  obtain ⟨k, C, rd⟩ := morphoReachMarketBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  have rdGuard := morphoBlocks.morpho_block_7351_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 1) hlen hbound hsize
  have rdReturn := morphoBlocks.morpho_block_7358_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have ret := morphoBlocks.morpho_block_7400
    (immWords := wordsOf (immStore v)) (by decide) rdReturn
  let mem := twoWordHashMem (calldataWord I.calldata 4) (UInt256.ofNat 3) solcFreePtrMem
  have hmem : mem.size = 96 := twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hload : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128 :=
    mloadFreePtrValue (by rw [hmem]; decide)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
  have hslot : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem =
      solcMappingSlot ⟨3⟩ (calldataWord I.calldata 4) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hmemdef : (UInt256.ofNat 3).toByteArray.write 0
      ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
        ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
        (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32 = mem := rfl
  rw [hmemdef, hload, hslot] at ret
  let words := (marketReturnEntries σ I (calldataWord I.calldata 4)).map (fun e => e.2.2)
  have hwrite : RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      ((writeCascade mem (returnWordWrites 128 words)).readWithPadding 128 (32 * words.length)) := by
    simpa only [words, marketReturnEntries, marketFieldWord, marketFieldSlot, halfWord, uint128Mask,
      List.map_cons, List.map_nil, returnWordWrites, writeCascade, Reasoning.Theory.writeWord,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using ret
  have hout : (writeCascade mem (returnWordWrites 128 words)).readWithPadding 128
      (32 * words.length) = returnWordBytes words :=
    readReturnWords_after_gap _ _ mem 128 (by rw [hmem]; decide)
      (by rw [hmem]; exact lt_usize _ (by decide))
  exact hout ▸ hwrite

set_option maxRecDepth 10000 in
theorem morphoMarketXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 23))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 23) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachMarketBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_7351_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 32) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 1) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 1) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_7358_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_7351_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

/-- `market(bytes32)`: the theorem `Correct.lean` routes selector 23 to. -/
theorem morphoMarketBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 23)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 23) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some marketTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · have hdec : decodeCalldataWithMode config.abiDecodeMode
          (marketTransition.params.map Param.name)
          (transitionSignature marketTransition).paramTypes I.calldata =
          some (marketArgs I.calldata) := by
        change decodeCalldata ["arg0"] [abiBytes32] I.calldata = _
        simpa only [marketArgs, calldataWord_toBytesBE I.calldata 4 hlen] using
          (decodeCalldata_bytes32_ok (x := "arg0") hlen hbound)
      by_cases hcv : I.weiValue = ⟨0⟩
      · apply reEquivSelectorExecution hcode
          (morphoMarketXReturns v hcode hsize hsel hcv hlen hbound) hd hdec
          (morphoMarketBodyReturns v _ hcv hbound)
        exact .returned rfl (morphoMarketReturnEncoding σ I _)
      · exact reEquivSelectorRevert hcode
          (morphoMarketXReverts v hcode hsize hsel (.inl hcv)) hd hdec
          (bodyReverts_nonPayable hcv)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoMarketXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_bytes32_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoMarketXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_bytes32_none_short hsz (by omega))

end Benchmarks.Morpho.MorphoBlue
