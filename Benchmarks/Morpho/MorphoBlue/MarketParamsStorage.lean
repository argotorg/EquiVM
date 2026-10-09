import Benchmarks.Morpho.MorphoBlue.MarketParamsCommon
import Benchmarks.Morpho.MorphoBlue.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: assignment through a resolved storage backend, including structs.
theorem assignStorageRef_backend {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {ref : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {value : Value}
    (hbase : frame.locals.get? ref.base = none)
    (her : evalStorageRef cfg frame evm ref = .ok er)
    (hty : storageTypeAt? frame.contract.storage er = some ty)
    (hwrite : cfg.storageBackend.write er ty value evm = .ok evm') :
    assignStorageRef? cfg frame evm .storage ref value = .ok (frame, evm') := by
  simp only [assignStorageRef?, resolveStorageRef?_ok hbase her hty,
    hwrite, bind, pure, EvalResult.bind]

-- LIBRARY CANDIDATE: a named struct write threads the state in field order.
theorem solidityWriteFields_cons {layout : StorageLayout} {evm evm' evm'' : EVM.State}
    {er : EvaledStorageRef} {name : Ident} {ty : StorageType} {value : Value}
    {types : List (Ident × StorageType)} {values : List (Ident × Value)}
    (hhead : solidityWriteStorage? layout evm
      { er with steps := er.steps ++ [.field name] } ty value = .ok evm')
    (htail : solidityWriteFields? layout evm' er types values = .ok evm'') :
    solidityWriteFields? layout evm er ((name, ty) :: types) ((name, value) :: values) =
      .ok evm'' := by
  simp only [solidityWriteFields?, if_pos rfl, ↓reduceIte, hhead, bind, EvalResult.bind, htail]

def marketParamsStorageType : StorageType := .struct "MarketParams"
  [("loanToken", .elem .address), ("collateralToken", .elem .address),
   ("oracle", .elem .address), ("irm", .elem .address),
   ("lltv", .elem (.int (.uint ⟨256, by decide⟩)))]

def MarketParamsWords.structValue (p : MarketParamsWords) : Value := .struct "MarketParams"
  [("loanToken", .address (AccountAddress.ofNat p.loanToken.toNat)),
   ("collateralToken", .address (AccountAddress.ofNat p.collateralToken.toNat)),
   ("oracle", .address (AccountAddress.ofNat p.oracle.toNat)),
   ("irm", .address (AccountAddress.ofNat p.irm.toNat)),
   ("lltv", .int (Int.ofNat p.lltv.toNat))]

def marketParamsStructExpr (e : Expr) : Expr := .structLit "MarketParams"
  [("loanToken", .tupleGet e 0), ("collateralToken", .tupleGet e 1),
   ("oracle", .tupleGet e 2), ("irm", .tupleGet e 3), ("lltv", .tupleGet e 4)]

theorem evalMarketParamsStruct {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} (p : MarketParamsWords) (he : evalExpr? cfg frame evm e = .ok p.value) :
    evalExpr? cfg frame evm (marketParamsStructExpr e) = .ok p.structValue := by
  simp only [marketParamsStructExpr, evalExpr?, evalStructFields?, he,
    MarketParamsWords.value, tupleGetValue?, bind, pure, EvalResult.bind, EvalResult.ofOption]
  rfl

def storeAddressWord (evm : EVM.State) (slot value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)

def storeMarketParams (evm : EVM.State) (id : UInt256) (p : MarketParamsWords) : EVM.State :=
  let s1 := storeAddressWord evm (marketParamsFieldSlot id 0) p.loanToken
  let s2 := storeAddressWord s1 (marketParamsFieldSlot id 1) p.collateralToken
  let s3 := storeAddressWord s2 (marketParamsFieldSlot id 2) p.oracle
  let s4 := storeAddressWord s3 (marketParamsFieldSlot id 3) p.irm
  Solm.EVM.storageStore s4 s4.executionEnv.codeOwner (marketParamsFieldSlot id 4) p.lltv

theorem writeMarketParamsAddress (evm : EVM.State) (id value : UInt256) (i : Fin 4)
    (hc : value.toNat < EVM.addressModulus) :
    solidityWriteStorage? Syntax.modelLayout evm
      ⟨"idToMarketParams", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id)),
        .field (marketParamsAddressField i)]⟩ (.elem .address)
      (.address (AccountAddress.ofNat value.toNat)) =
        .ok (storeAddressWord evm (marketParamsFieldSlot id i) value) := by
  exact solidityStorageBackend_write_elem _ _ _ _ _ _ _
    (morphoLayout_marketParamsAddress id i) (storageLocStore_address_offset0 evm _ value hc)

theorem writeMarketParams (evm : EVM.State) (id : UInt256) (p : MarketParamsWords)
    (hc : p.Canonical) :
    config.storageBackend.write
      ⟨"idToMarketParams", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))]⟩
      marketParamsStorageType p.structValue evm = .ok (storeMarketParams evm id p) := by
  change solidityWriteStorage? Syntax.modelLayout evm _ _ _ = _
  rw [marketParamsStorageType, MarketParamsWords.structValue, solidityWriteStorage?]
  simp only [↓reduceIte]
  apply solidityWriteFields_cons (writeMarketParamsAddress _ id p.loanToken ⟨0, by decide⟩ hc.1)
  apply solidityWriteFields_cons (writeMarketParamsAddress _ id p.collateralToken ⟨1, by decide⟩ hc.2.1)
  apply solidityWriteFields_cons (writeMarketParamsAddress _ id p.oracle ⟨2, by decide⟩ hc.2.2.1)
  apply solidityWriteFields_cons (writeMarketParamsAddress _ id p.irm ⟨3, by decide⟩ hc.2.2.2)
  apply solidityWriteFields_cons
    (solidityStorageBackend_write_elem _ _ _ _ _ _ _ (morphoLayout_marketParamsLltv id)
      (storageLocStore_uint256 _ _ p.lltv))
  simp only [solidityWriteFields?]
  rfl

theorem assignMarketParams (evm : EVM.State) (locals imms : Store) (key : Expr)
    (id : UInt256) (p : MarketParamsWords) (hc : p.Canonical)
    (hbase : locals.get? "idToMarketParams" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"idToMarketParams", [.mindex key]⟩ p.structValue =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeMarketParams evm id p) := by
  apply assignStorageRef_backend hbase (evalStorageRef_mindex hkey ?_) rfl
    (writeMarketParams evm id p hc)
  simp only [valueToKey?, word_toBytesBE_length_32,
    if_pos (by decide : (32 : Nat) = 31 + 1), ↓reduceIte, pure]

theorem storeMarketParams_executionEnv (evm : EVM.State) (id : UInt256) (p : MarketParamsWords) :
    (storeMarketParams evm id p).executionEnv = evm.executionEnv := by
  simp only [storeMarketParams, storeAddressWord, storageStore_executionEnv]

end Benchmarks.Morpho.MorphoBlue
