import Benchmarks.CompoundIII.Comet.ConstructorFactoryCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def createAssetListHeaderExpr : Expr :=
  .abiEncodePacked [(.elem (.bytes ⟨3, by decide⟩),
    .fixedBytesLit ⟨3, by decide⟩ [186, 21, 185, 209]),
    (abiUInt256, .intLit 32), (abiUInt256, .arrayLength .localVar ⟨"assets", []⟩)]

def createAssetListWordExpr (j : Nat) : Expr :=
  if j < 2 then .cast (.tupleGet (.var "entry") j) (.elem (.int (.uint ⟨256, by decide⟩)))
  else .tupleGet (.var "entry") j

def createAssetListAppendExpr : Expr :=
  .abiEncodePacked [(.bytes, .var "payload"),
    (abiUInt256, createAssetListWordExpr 0), (abiUInt256, createAssetListWordExpr 1),
    (abiUInt256, createAssetListWordExpr 2), (abiUInt256, createAssetListWordExpr 3),
    (abiUInt256, createAssetListWordExpr 4), (abiUInt256, createAssetListWordExpr 5),
    (abiUInt256, createAssetListWordExpr 6)]

def createAssetListLoopCond : Expr :=
  .binary .lt (.var "index") (.arrayLength .localVar ⟨"assets", []⟩)

def createAssetListLoopBody : List Stmt :=
  [.letDecl "entry" none (.index (.var "assets") (.var "index")),
    .assign .localVar ⟨"payload", []⟩ createAssetListAppendExpr,
    .assign .localVar ⟨"index", []⟩ (.binary .add (.var "index") (.intLit 1))]

def createAssetListPrefix : List Stmt :=
  [.letDecl "payload" (some .bytes) createAssetListHeaderExpr,
    .letDecl "index" (some abiUInt256) (.intLit 0),
    .while createAssetListLoopCond createAssetListLoopBody]

def createAssetListRemainder : List Stmt :=
  [.lowLevelCall (.var "factory") (.intLit 0) (.var "payload") "ok" "result",
    .require (.var "ok"),
    .letDecl "resultAddress" (some abiAddress) (.abiDecode abiAddress (.var "result")),
    .return [.var "resultAddress"]]

def createAssetListCallable : CallableDecl :=
  { params := [⟨"factory", abiAddress⟩, ⟨"assets", .dynamicArray ConstructorAsset.abiType⟩]
    returnType := [abiAddress]
    body := createAssetListPrefix ++ createAssetListRemainder }

theorem createAssetListCallable_lookup :
    lookupCallable? contract "createAssetList_call" = some createAssetListCallable := rfl

def createAssetListHeader (n : Nat) : ByteArray :=
  ⟨([186, 21, 185, 209] ++ EVM.Word.toBytesBE (UInt256.ofNat 32) ++
    EVM.Word.toBytesBE (UInt256.ofNat n)).toArray⟩

def createAssetListPayload (assets : List ConstructorAsset) (i : Nat) : ByteArray :=
  createAssetListHeader assets.length ++ wordBytes ((assets.take i).flatMap ConstructorAsset.words)

theorem createAssetListPayload_zero (assets : List ConstructorAsset) :
    createAssetListPayload assets 0 = createAssetListHeader assets.length := by
  simp only [createAssetListPayload, List.take_zero, List.flatMap_nil, wordBytes,
    ByteArray.append_empty]

theorem createAssetListPayload_succ {assets : List ConstructorAsset} {i : Nat}
    (hi : i < assets.length) :
    createAssetListPayload assets (i + 1) =
      createAssetListPayload assets i ++ wordBytes assets[i].words := by
  simp only [createAssetListPayload, List.take_succ_eq_append_getElem hi, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, wordBytes_append, ByteArray.append_assoc]

def createAssetListEntry (imms : Store) (factory : AccountAddress)
    (assets : List ConstructorAsset) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "assets" (.array (assets.map ConstructorAsset.value))).insert
      "factory" (.address factory)
    immutables := imms }

end Benchmarks.CompoundIII.Comet
