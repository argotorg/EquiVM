import Benchmarks.CompoundIII.Comet.CreateAssetListSyntax

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem createAssetListLength_eval {frame : Frame} {evm : EVM.State}
    {assets : List ConstructorAsset}
    (ha : frame.locals.get? "assets" = some (.array (assets.map ConstructorAsset.value))) :
    evalExpr? config frame evm (.arrayLength .localVar ⟨"assets", []⟩) =
      .ok (.int (Int.ofNat assets.length)) := by
  simp only [evalExpr?, ha, readLocalPath?, pure, bind, EvalResult.bind, List.length_map,
    Int.ofNat_eq_natCast]

theorem createAssetListHeader_eval {frame : Frame} {evm : EVM.State}
    {assets : List ConstructorAsset}
    (ha : frame.locals.get? "assets" = some (.array (assets.map ConstructorAsset.value)))
    (hn : assets.length < UInt256.size) :
    evalExpr? config frame evm createAssetListHeaderExpr =
      .ok (.bytes (createAssetListHeader assets.length)) := by
  have hc := createAssetListLength_eval (evm := evm) ha
  have he : evalExpr? config frame evm (.arrayLength .localVar ⟨"assets", []⟩) =
      .ok (.int (Int.ofNat (UInt256.ofNat assets.length).toNat)) := by
    rw [UInt256.toNat_ofNat_of_lt hn]
    exact hc
  have hf : encodePackedValue? (.elem (.bytes ⟨3, by decide⟩))
      (.fixedBytes ⟨3, by decide⟩ [186, 21, 185, 209]) = some [186, 21, 185, 209] := by decide
  have hp := evalPackedArgs_cons (show evalExpr? config frame evm
    (.fixedBytesLit ⟨3, by decide⟩ [186, 21, 185, 209]) =
      .ok (.fixedBytes ⟨3, by decide⟩ [186, 21, 185, 209]) by simp only [evalExpr?, pure]) hf
    (evalPackedArgs_cons (show evalExpr? config frame evm (.intLit 32) =
      .ok (.int (Int.ofNat (UInt256.ofNat 32).toNat)) by simp only [evalExpr?, pure]; rfl)
        (encodePacked_uint256 _)
      (evalPackedArgs_single he (encodePacked_uint256 _)))
  rw [createAssetListHeaderExpr, evalExpr?, hp]
  simp only [createAssetListHeader, List.append_assoc]
  rfl

theorem createAssetListWord_eval {frame : Frame} {evm : EVM.State} {a : ConstructorAsset}
    {j : Nat} (hj : j < 7)
    (he : evalExpr? config frame evm (.var "entry") = .ok a.value) :
    evalExpr? config frame evm (createAssetListWordExpr j) =
      .ok (.int (Int.ofNat (a.word j).toNat)) := by
  have h0 := a.asset.isLt
  have h1 := a.priceFeed.isLt
  have h2 := a.decimals.isLt
  have h3 := a.borrowCollateralFactor.isLt
  have h4 := a.liquidateCollateralFactor.isLt
  have h5 := a.liquidationFactor.isLt
  have h6 := a.supplyCap.isLt
  unfold AccountAddress.size at h0 h1
  have ha0 : a.asset.val < 2^256 := by omega
  have ha1 : a.priceFeed.val < 2^256 := by omega
  norm_num at ha0 ha1
  have hw (n : Nat) (hn : n < 2^256) : (EVM.word n).toNat = n :=
    UInt256.toNat_ofNat_of_lt hn
  interval_cases j <;>
    simp (disch := omega) [createAssetListWordExpr, evalExpr?, he, ConstructorAsset.value,
      ConstructorAsset.scalars, ConstructorAsset.word, ConstructorAsset.words,
      constructorAddressScalar, constructorUintScalar, tupleGetValue?, bind,
      EvalResult.bind, castValue?, EVM.twoPow, hw, ha0, ha1,
      List.getElem?_cons_zero, EvalResult.ofOption]

theorem createAssetListAppend_eval {frame : Frame} {evm : EVM.State} {a : ConstructorAsset}
    {payload : ByteArray}
    (he : evalExpr? config frame evm (.var "entry") = .ok a.value)
    (hp : evalExpr? config frame evm (.var "payload") = .ok (.bytes payload)) :
    evalExpr? config frame evm createAssetListAppendExpr =
      .ok (.bytes (payload ++ wordBytes a.words)) := by
  have h0 := createAssetListWord_eval (j := 0) (by decide) he
  have h1 := createAssetListWord_eval (j := 1) (by decide) he
  have h2 := createAssetListWord_eval (j := 2) (by decide) he
  have h3 := createAssetListWord_eval (j := 3) (by decide) he
  have h4 := createAssetListWord_eval (j := 4) (by decide) he
  have h5 := createAssetListWord_eval (j := 5) (by decide) he
  have h6 := createAssetListWord_eval (j := 6) (by decide) he
  have hs := evalPackedArgs_cons hp (show encodePackedValue? .bytes (.bytes payload) =
    some payload.toList by rfl)
    (evalPackedArgs_cons h0 (encodePacked_uint256 _)
    (evalPackedArgs_cons h1 (encodePacked_uint256 _)
    (evalPackedArgs_cons h2 (encodePacked_uint256 _)
    (evalPackedArgs_cons h3 (encodePacked_uint256 _)
    (evalPackedArgs_cons h4 (encodePacked_uint256 _)
    (evalPackedArgs_cons h5 (encodePacked_uint256 _)
    (evalPackedArgs_single h6 (encodePacked_uint256 _))))))))
  rw [createAssetListAppendExpr, evalExpr?, hs]
  change EvalResult.ok (Value.bytes _) = EvalResult.ok (Value.bytes _)
  congr 2
  rw [wordBytes_eq_list, bytearray_append_list_eq]
  simp only [ConstructorAsset.words, ConstructorAsset.scalars,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ConstructorAsset.word, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

end Benchmarks.CompoundIII.Comet
