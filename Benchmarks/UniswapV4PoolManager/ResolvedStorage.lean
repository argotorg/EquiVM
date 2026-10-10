import Benchmarks.UniswapV4PoolManager.PoolStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: resolve a mapping index through a local mapping storage alias.
theorem resolveStorageAliasMapping {cfg : Config} {f : Frame} {evm : EVM.State}
    {name : Ident} {er : EvaledStorageRef} {ty : StorageType} {kt : ElemType}
    {e : Expr} {value : Value} {key : KeyValue}
    (hs : f.locals.get? name = some (.storageRef er (.mapping kt ty)))
    (he : evalExpr? cfg f evm e = .ok value) (hk : valueToKey? value = some key) :
    resolveStorageRef? cfg f evm {base := name, steps := [.mindex e]} =
      .ok ({er with steps := er.steps ++ [.mindex key]}, ty) := by
  simp only [resolveStorageRef?, hs, evalStorageRefFrom?, evalStorageRefStep, he, hk,
    storageTypeStep?, bind, EvalResult.bind, pure, EvalResult.ofOption]

-- LIBRARY CANDIDATE: resolve a mapping field through a local struct storage alias.
theorem resolveStorageAliasFieldMapping {cfg : Config} {f : Frame} {evm : EVM.State}
    {name field : Ident} {er : EvaledStorageRef} {ty ty' : StorageType} {kt : ElemType}
    {e : Expr} {value : Value} {key : KeyValue}
    (hs : f.locals.get? name = some (.storageRef er ty))
    (ht : storageTypeStep? ty (.field field) = some (.mapping kt ty'))
    (he : evalExpr? cfg f evm e = .ok value) (hk : valueToKey? value = some key) :
    resolveStorageRef? cfg f evm {base := name, steps := [.field field, .mindex e]} =
      .ok ({er with steps := er.steps ++ [.field field, .mindex key]}, ty') := by
  have hm : storageTypeStep? (.mapping kt ty') (.mindex key) = some ty' := rfl
  simp only [resolveStorageRef?, hs, evalStorageRefFrom?, evalStorageRefStep, he, hk, ht,
    hm, bind, EvalResult.bind, pure, EvalResult.ofOption, List.append_assoc,
    List.cons_append, List.nil_append]

-- GENERALIZES scalar storage reads to any already-resolved reference and location.
theorem readResolvedStorageScalar {cfg : Config} {layout : StorageLayout} {f : Frame} {evm : EVM.State}
    {ref : StorageRef} {er : EvaledStorageRef} {t : ElemType} {loc : StorageLoc}
    (hr : resolveStorageRef? cfg f evm ref = .ok (er, .elem t))
    (hb : cfg.storageBackend = solidityStorageBackend layout)
    (hl : layout er = some (.leaf loc)) :
    evalExpr? cfg f evm (.storage ref) = .ok (storageLocLoad evm loc) := by
  rw [evalExpr?, hr]
  simp only [bind, EvalResult.bind]
  exact readStorage?_elem hb hl

end Benchmarks.UniswapV4PoolManager
