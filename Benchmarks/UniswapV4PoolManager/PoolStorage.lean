import Benchmarks.UniswapV4PoolManager.PoolKeySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolStateType : StorageType := match contract.storage[7]!.ty with
  | .mapping _ ty => ty
  | _ => .elem .bool
def poolRef (id : UInt256) : EvaledStorageRef :=
  {base := "_pools", steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))]}
def poolSlot0Ref (id : UInt256) : EvaledStorageRef :=
  {base := "_pools", steps := (poolRef id).steps ++ [.field "slot0"]}
def poolRefValue (id : UInt256) : Value := .storageRef (poolRef id) poolStateType
def poolSlot (id : UInt256) : UInt256 := mappingSlotWord id ⟨6⟩
def poolSlot0Word (evm : EVM.State) (id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (poolSlot id)

theorem poolRef_type (id : UInt256) : storageTypeAt? contract.storage (poolRef id) = some poolStateType := rfl
theorem poolState_slot0_type : storageTypeStep? poolStateType (.field "slot0") =
    some (.elem (.bytes abiBytes32Width)) := rfl

theorem poolSlot0_loc (id : UInt256) : config.storageBackend.locate? (poolSlot0Ref id) =
    some (.leaf (bytes32Loc (poolSlot id))) := by
  simp only [poolSlot0Ref, poolRef, config, storageBackend, solidityStorageBackend,
    List.cons_append, List.nil_append]
  have hk : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id :=
    keyValueToWord_fixedBytes32 id
  rw [hk]
  rfl

theorem poolMappingResolve {f : Frame} {evm : EVM.State} {e : Expr} {id : UInt256}
    (hf : f.contract = contract) (hb : f.locals.get? "_pools" = none)
    (he : evalExpr? config f evm e = .ok (wordBytes32Value id)) :
    resolveStorageRef? config f evm {base := "_pools", steps := [.mindex e]} =
      .ok (poolRef id, poolStateType) := by
  apply resolveStorageRef?_ok hb (evalMappingRef he (by
    simp only [valueToKey?, word_toBytesBE_length_32]
    rfl))
  rw [hf]; exact poolRef_type id

-- LIBRARY CANDIDATE: resolving a local storage alias without additional steps.
theorem resolveStorageAlias {cfg : Config} {f : Frame} {evm : EVM.State}
    {name : Ident} {er : EvaledStorageRef} {ty : StorageType}
    (hs : f.locals.get? name = some (.storageRef er ty)) :
    resolveStorageRef? cfg f evm {base := name} = .ok (er, ty) := by
  simp only [resolveStorageRef?, hs, evalStorageRefFrom?, pure]

-- LIBRARY CANDIDATE: resolving one field through a local storage alias.
theorem resolveStorageAliasField {cfg : Config} {f : Frame} {evm : EVM.State}
    {name field : Ident} {er : EvaledStorageRef} {ty ty' : StorageType}
    (hs : f.locals.get? name = some (.storageRef er ty))
    (ht : storageTypeStep? ty (.field field) = some ty') :
    resolveStorageRef? cfg f evm {base := name, steps := [.field field]} =
      .ok ({er with steps := er.steps ++ [.field field]}, ty') := by
  simp only [resolveStorageRef?, hs, evalStorageRefFrom?, evalStorageRefStep, ht,
    bind, EvalResult.bind, pure, EvalResult.ofOption]

theorem poolSlot0_read {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256}
    (hs : f.locals.get? name = some (poolRefValue id)) :
    evalExpr? config f evm (.storage {base := name, steps := [.field "slot0"]}) =
      .ok (wordBytes32Value (poolSlot0Word evm id)) := by
  rw [evalExpr?, resolveStorageAliasField hs poolState_slot0_type]
  simp only [bind, EvalResult.bind]
  have hr := readStorage?_elem (cfg := config) (evm := evm) (er := poolSlot0Ref id)
    (t := .bytes abiBytes32Width) (hbackend := rfl) (hloc := poolSlot0_loc id)
  rw [storageLocLoad_bytes32] at hr
  exact hr

-- GENERALIZES Reasoning.Theory.assignStorageRef_storage_scalar_value to resolved storage aliases.
theorem assignResolvedStorageScalar {cfg : Config} {layout : StorageLayout} {f : Frame} {evm evm' : EVM.State}
    {ref : StorageRef} {er : EvaledStorageRef} {t : ElemType} {loc : StorageLoc} {value : Value}
    (hr : resolveStorageRef? cfg f evm ref = .ok (er, .elem t))
    (hb : cfg.storageBackend = solidityStorageBackend layout)
    (hl : layout er = some (.leaf loc)) (hs : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg f evm .storage ref value = .ok (f, evm') := by
  simp only [assignStorageRef?, hr, bind, EvalResult.bind, hb, solidityStorageBackend,
    solidityWriteStorage?, solidityLeafLoc?_of_leaf hl, hs, EvalResult.ofOption, pure]

theorem poolSlot0_write {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256}
    (hs : f.locals.get? name = some (poolRefValue id)) (word : UInt256) :
    assignStorageRef? config f evm .storage {base := name, steps := [.field "slot0"]} (wordBytes32Value word) =
      .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolSlot id) word) := by
  exact assignResolvedStorageScalar (resolveStorageAliasField hs poolState_slot0_type) rfl
    (poolSlot0_loc id) (storageLocStore_bytes32 evm _ word _ (valueToWord_bytes32_word word))

end Benchmarks.UniswapV4PoolManager
