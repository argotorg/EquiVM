import Benchmarks.CompoundIII.Comet.CreateAssetListPayload
import Benchmarks.CompoundIII.Comet.Solc0815Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

structure CreateAssetListLoopState (factory : AccountAddress) (assetConfigs : List ConstructorAsset)
    (i : Nat) (frame : Frame) : Prop where
  factory : frame.locals.get? "factory" = some (.address factory)
  assets : frame.locals.get? "assets" = some (.array (assetConfigs.map ConstructorAsset.value))
  index : frame.locals.get? "index" = some (.int (Int.ofNat i))
  payload : frame.locals.get? "payload" = some (.bytes (createAssetListPayload assetConfigs i))

theorem CreateAssetListLoopState.condition {factory : AccountAddress}
    {assets : List ConstructorAsset} {i : Nat} {frame : Frame}
    (h : CreateAssetListLoopState factory assets i frame) (evm : EVM.State) :
    evalExpr? config frame evm createAssetListLoopCond =
      .ok (.bool (decide (i < assets.length))) := by
  have hi : evalExpr? config frame evm (.var "index") = .ok (.int (Int.ofNat i)) := by
    simp only [evalExpr?, h.index, EvalResult.ofOption]
  simp only [createAssetListLoopCond, evalExpr?, hi, createAssetListLength_eval h.assets,
    bind, EvalResult.bind, evalBinaryOp?]
  simp

theorem CreateAssetListLoopState.entry {factory : AccountAddress} {assets : List ConstructorAsset}
    {i : Nat} {frame : Frame} (h : CreateAssetListLoopState factory assets i frame)
    (evm : EVM.State) (hi : i < assets.length) :
    evalExpr? config frame evm (.index (.var "assets") (.var "index")) = .ok assets[i].value := by
  simp only [evalExpr?, h.assets, h.index, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?]
  have hb : 0 ≤ Int.ofNat i ∧ Int.ofNat i < (assets.map ConstructorAsset.value).length := by
    simp only [List.length_map, Int.ofNat_eq_natCast]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hi⟩
  rw [if_pos hb]
  change (match lookupNth? (assets.map ConstructorAsset.value) i with
    | some v => normalizeRawBoolWord? v | none => .error .typeError) = _
  rw [lookupNth_eq_getElem?, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

def createAssetListNextFrame (frame : Frame) (assets : List ConstructorAsset) (i : Nat)
    (hi : i < assets.length) : Frame :=
  let locals := frame.locals.insert "entry" assets[i].value
  let locals := locals.insert "payload" (.bytes (createAssetListPayload assets (i + 1)))
  { frame with locals := locals.insert "index" (.int (Int.ofNat (i + 1))) }

theorem CreateAssetListLoopState.next {factory : AccountAddress} {assets : List ConstructorAsset}
    {i : Nat} {frame : Frame} (h : CreateAssetListLoopState factory assets i frame)
    (hi : i < assets.length) :
    CreateAssetListLoopState factory assets (i + 1)
      (createAssetListNextFrame frame assets i hi) := by
  constructor
  · simpa [createAssetListNextFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using h.factory
  · simpa [createAssetListNextFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using h.assets
  · simp only [createAssetListNextFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  · simp only [createAssetListNextFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl

theorem createAssetListLoop_step {factory : AccountAddress} {assets : List ConstructorAsset}
    {i : Nat} {frame : Frame} (h : CreateAssetListLoopState factory assets i frame)
    (evm : EVM.State) (hi : i < assets.length) :
    ExecBlock config frame evm createAssetListLoopBody
      (.ok (createAssetListNextFrame frame assets i hi) evm) := by
  refine .consNormal (.letDecl (h.entry evm hi)) ?_
  refine .consNormal (solm' := { frame with locals :=
    ((frame.locals.insert "entry" assets[i].value).insert "payload"
      (.bytes (createAssetListPayload assets (i + 1)))) }) (evm' := evm)
    (.assign (value := .bytes (createAssetListPayload assets (i + 1))) ?_ ?_) ?_
  · rw [createAssetListPayload_succ hi]
    apply createAssetListAppend_eval
    · simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    · simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      change EvalResult.ofOption .unboundVariable (frame.locals.get? "payload") = _
      rw [h.payload]
      rfl
  · simp only [assignStorageRef?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    change (match frame.locals.get? "payload" with
      | some root => _ | none => _) = _
    rw [h.payload]
    simp only [updateLocalPath?, pure, bind, EvalResult.bind]
  dsimp only
  refine .consNormal (.assign (value := .int (Int.ofNat (i + 1))) ?_ ?_) .nil
  · simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    change (show EvalResult Value from do
      let v ← EvalResult.ofOption .unboundVariable (frame.locals.get? "index")
      evalBinaryOp? .add v (.int 1)) = _
    rw [h.index]
    simp [EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
  · simp only [assignStorageRef?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    change (match frame.locals.get? "index" with
      | some root => _ | none => _) = _
    rw [h.index]
    simp only [updateLocalPath?, pure, bind, EvalResult.bind]
    rfl

theorem createAssetListLoop_exec {factory : AccountAddress} {assets : List ConstructorAsset}
    {i : Nat} {frame : Frame} (h : CreateAssetListLoopState factory assets i frame)
    (evm : EVM.State) (hi : i ≤ assets.length) :
    ∃ frame', ExecStmt config frame evm (.while createAssetListLoopCond createAssetListLoopBody)
      (.ok frame' evm) ∧ CreateAssetListLoopState factory assets assets.length frame' := by
  generalize hv : assets.length - i = v
  induction v generalizing i frame with
  | zero =>
    have he : i = assets.length := by omega
    subst i
    exact ⟨frame, .whileFalse (by rw [h.condition]; simp), h⟩
  | succ v ih =>
    have hi' : i < assets.length := by omega
    obtain ⟨frame', hr, hs⟩ := ih (h.next hi') (by omega) (by omega)
    exact ⟨frame', .whileTrue (by rw [h.condition, decide_eq_true hi'])
      (createAssetListLoop_step h evm hi') hr, hs⟩

end Benchmarks.CompoundIII.Comet
