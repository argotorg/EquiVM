import Benchmarks.Morpho.MorphoBlue.Routines
import Benchmarks.Morpho.MorphoBlue.ReturnCommon
import Benchmarks.Morpho.MorphoBlue.Storage

/-!
# Morpho `position(bytes32,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4366; reach lemma `morphoReachPositionBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

def positionReturnEntries (σ : AccountMap) (I : ExecutionEnv) (id account : UInt256) :
    List (ElemType × Value × UInt256) :=
  ([0, 1, 2] : List (Fin 3)).map fun i =>
    let w := positionFieldWord σ I id account i
    (if i.val = 0 then .int (.uint ⟨256, by decide⟩) else .int (.uint ⟨128, by decide⟩),
      .int (Int.ofNat w.toNat), w)

def positionArgs (cd : ByteArray) : Store :=
  ((∅ : Store).insert "arg0" (.fixedBytes ⟨31, by decide⟩
    (EVM.Word.toBytesBE (calldataWord cd 4)))).insert "arg1"
      (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))

theorem morphoPositionBodyReturns (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 36).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (positionArgs evm.executionEnv.calldata)
      positionTransition.body
      (.returned
        { contract := contract,
          locals := (positionArgs evm.executionEnv.calldata).insert "__calldata"
            (.bytes evm.executionEnv.calldata), immutables := immStore v }
        evm (some ((positionReturnEntries evm.accountMap evm.executionEnv
          (calldataWord evm.executionEnv.calldata 4)
          (calldataWord evm.executionEnv.calldata 36)).map (fun e => e.2.1)))) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (calldataPrelude_ok hcv hsize).run
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hbase : ((positionArgs evm.executionEnv.calldata).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).get? "position" = none := by simp [positionArgs]
  have hkey0 : evalExpr? config
      { contract := contract,
        locals := (positionArgs evm.executionEnv.calldata).insert "__calldata"
          (.bytes evm.executionEnv.calldata), immutables := immStore v }
      evm (.var "arg0") =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (calldataWord evm.executionEnv.calldata 4))) := by
    simp only [evalExpr?, positionArgs,
      store_get_ne (k := "__calldata") (a := "arg0") _ _ (by decide),
      store_get_ne (k := "arg1") (a := "arg0") _ _ (by decide),
      store_get_self, EvalResult.ofOption]
  have hkey1 : evalExpr? config
      { contract := contract,
        locals := (positionArgs evm.executionEnv.calldata).insert "__calldata"
          (.bytes evm.executionEnv.calldata), immutables := immStore v }
      evm (.var "arg1") =
      .ok (.address (AccountAddress.ofNat (calldataWord evm.executionEnv.calldata 36).toNat)) := by
    simp only [evalExpr?, positionArgs,
      store_get_ne (k := "__calldata") (a := "arg1") _ _ (by decide),
      store_get_self, EvalResult.ofOption]
  have he (i : Fin 3) := evalMorphoPositionField evm _ (immStore v) (.var "arg0") (.var "arg1")
    (calldataWord evm.executionEnv.calldata 4) (calldataWord evm.executionEnv.calldata 36)
    i hbase hkey0 hkey1 hcanon
  have h0 := he ⟨0, by decide⟩
  have h1 := he ⟨1, by decide⟩
  have h2 := he ⟨2, by decide⟩
  simp only [positionFieldName] at h0 h1 h2
  simp only [evalExprs?, positionReturnEntries, List.map_cons, List.map_nil,
    h0, h1, h2, pure, bind, EvalResult.bind]
  rfl

theorem morphoPositionReturnEncoding (σ : AccountMap) (I : ExecutionEnv) (id account : UInt256) :
    encodeReturnValues? positionTransition.returnType
      ((positionReturnEntries σ I id account).map (fun e => e.2.1)) =
      some (returnWordBytes ((positionReturnEntries σ I id account).map (fun e => e.2.2))) := by
  apply elementaryWordsReturnEncoding (positionReturnEntries σ I id account)
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  fin_cases i
  · exact encodeABIValue_uint256 _
  · exact encodeABIValue_uint _ _ (halfWord_bound false _)
  · exact encodeABIValue_uint _ _ (halfWord_bound true _)

set_option maxRecDepth 10000 in
theorem morphoPositionReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 12))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11424)
      [UInt256.ofNat 4445, ⟨64⟩, solcAddrMask, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachPositionBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  have rdGuard := morphoBlocks.morpho_block_4366_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 2) hlen hbound hsize
  have rdCall := morphoBlocks.morpho_block_4373_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have rdDecode := morphoBlocks.morpho_block_4415
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCall
  exact ⟨_, _, rdDecode⟩

set_option maxRecDepth 10000 in
theorem morphoPositionXReturns {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 12))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (returnWordBytes ((positionReturnEntries σ I (calldataWord I.calldata 4)
        (calldataWord I.calldata 36)).map (fun e => e.2.2))) := by
  obtain ⟨k, C, rd⟩ := morphoPositionReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound
  obtain ⟨k', C', rdReturn⟩ := morphoDecodeAddress36Ok (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hcanon rd
  have ret := morphoBlocks.morpho_block_4445
    (immWords := wordsOf (immStore v)) (by decide) rdReturn
  let mem0 := twoWordHashMem (calldataWord I.calldata 4) (UInt256.ofNat 2) solcFreePtrMem
  have hmem0def : (UInt256.ofNat 2).toByteArray.write 0
      ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
        solcFreePtrMem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32 = mem0 := rfl
  rw [hmem0def] at ret
  have hslot0 : keccakWord ⟨0⟩ ⟨64⟩ mem0 =
      solcMappingSlot ⟨2⟩ (calldataWord I.calldata 4) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hslot0] at ret
  let mem := twoWordHashMem (calldataWord I.calldata 36)
    (solcMappingSlot ⟨2⟩ (calldataWord I.calldata 4)) mem0
  have hmemdef : (solcMappingSlot ⟨2⟩ (calldataWord I.calldata 4)).toByteArray.write 0
      ((UInt256.land (calldataWord I.calldata 36) solcAddrMask).toByteArray.write 0
        mem0 (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32 = mem := by
    rw [solcAddrMask_clean hcanon]
    rfl
  rw [hmemdef] at ret
  have hmem0 : mem0.size = 96 := twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hmem : mem.size = 96 := twoWordHashMem_size_96 _ _ hmem0
  have hload : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128 :=
    mloadFreePtrValue (by rw [hmem]; decide)
      (twoWordHashMem_read64 _ _ hmem0
        (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
  have hslot : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem =
      positionSlot (calldataWord I.calldata 4) (calldataWord I.calldata 36) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hload, hslot] at ret
  let words := (positionReturnEntries σ I (calldataWord I.calldata 4)
    (calldataWord I.calldata 36)).map (fun e => e.2.2)
  have hwrite : RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      ((writeCascade mem (returnWordWrites 128 words)).readWithPadding 128 (32 * words.length)) := by
    simpa only [words, positionReturnEntries, positionFieldWord, halfWord, uint128Mask,
      List.map_cons, List.map_nil, returnWordWrites, writeCascade, Reasoning.Theory.writeWord] using ret
  have hout : (writeCascade mem (returnWordWrites 128 words)).readWithPadding 128
      (32 * words.length) = returnWordBytes words :=
    readReturnWords_after_gap _ _ mem 128 (by rw [hmem]; decide)
      (by rw [hmem]; exact lt_usize _ (by decide))
  exact hout ▸ hwrite

set_option maxRecDepth 10000 in
theorem morphoPositionXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 12))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 12) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachPositionBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_4366_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 64) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 2) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 2) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_4373_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_4366_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

set_option maxRecDepth 10000 in
theorem morphoPositionXNoncanonical {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 12)) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases hcv : I.weiValue = ⟨0⟩
  · obtain ⟨k, C, rd⟩ := morphoPositionReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound
    exact morphoDecodeAddress36Revert (by decide) hnc rd
  · exact morphoPositionXReverts v hcode hsize hsel (.inl hcv)

/-- `position(bytes32,address)`: the theorem `Correct.lean` routes selector 12 to. -/
theorem morphoPositionBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 12)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 12) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some positionTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 68 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (positionTransition.params.map Param.name)
            (transitionSignature positionTransition).paramTypes I.calldata =
            some (positionArgs I.calldata) := by
          change decodeCalldata ["arg0", "arg1"] [abiBytes32, .elem .address] I.calldata = _
          simpa only [positionArgs, calldataWord_toBytesBE I.calldata 4 (by omega)] using
            (decodeCalldata_bytes32_address_ok (x := "arg0") (y := "arg1") hlen hbound hcanon)
        by_cases hcv : I.weiValue = ⟨0⟩
        · apply reEquivSelectorExecution hcode
            (morphoPositionXReturns v hcode hsize hsel hcv hlen hbound hcanon) hd hdec
            (morphoPositionBodyReturns v _ hcv hbound hcanon)
          exact .returned rfl (morphoPositionReturnEncoding σ I _ _)
        · exact reEquivSelectorRevert hcode
            (morphoPositionXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · exact reEquivSelectorDecodingFailed hcode
          (morphoPositionXNoncanonical v hcode hsize hsel hlen hbound hcanon) hd
          (decodeCalldata_bytes32_address_none_noncanon hlen hbound hcanon)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoPositionXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_bytes32_address_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoPositionXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_bytes32_address_none_short hsz (by omega))

end Benchmarks.Morpho.MorphoBlue
