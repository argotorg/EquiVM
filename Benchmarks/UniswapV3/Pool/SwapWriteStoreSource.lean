import Benchmarks.UniswapV3.Pool.SwapWriteCall
import Benchmarks.UniswapV3.Pool.SwapSlotStorage
import Benchmarks.UniswapV3.Pool.SourceTuples

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def swapWriteIndexFrame (frame : Frame) (index : UInt256) : Frame :=
  {frame with locals := frame.locals.insert "observationIndex" (.int (Int.ofNat index.toNat))}

def swapWriteCardinalityFrame (frame : Frame) (index cardinality : UInt256) : Frame :=
  let f := swapWriteIndexFrame frame index
  {f with locals := f.locals.insert "observationCardinality" (.int (Int.ofNat cardinality.toNat))}

def swapWritePriceFrame (frame : Frame) (s : SwapStateData) (index cardinality : UInt256) : Frame :=
  let f := swapWriteCardinalityFrame frame index cardinality
  {f with locals := f.locals.insert "__t17" (.int (Int.ofNat s.price.toNat))}

def swapWriteTickFrame (frame : Frame) (s : SwapStateData) (index cardinality : UInt256) : Frame :=
  let f := swapWritePriceFrame frame s index cardinality
  {f with locals := f.locals.insert "__t18" (.int s.tick)}

def swapWriteIndexTempFrame (frame : Frame) (s : SwapStateData)
    (index cardinality : UInt256) : Frame :=
  let f := swapWriteTickFrame frame s index cardinality
  {f with locals := f.locals.insert "__t19" (.int (Int.ofNat index.toNat))}

def swapWriteStoreFrame (frame : Frame) (s : SwapStateData) (index cardinality : UInt256) : Frame :=
  let f := swapWriteIndexTempFrame frame s index cardinality
  {f with locals := f.locals.insert "__t20" (.int (Int.ofNat cardinality.toNat))}

macro "swap_write_temp_get" : tactic =>
  `(tactic| (simp only [swapWriteStoreFrame, swapWriteIndexTempFrame, swapWriteTickFrame,
    swapWritePriceFrame, swapWriteCardinalityFrame, swapWriteIndexFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; try rfl))

theorem swapWriteStoreFrame_parts (frame : Frame) (s : SwapStateData)
    (index cardinality : UInt256) :
    (swapWriteStoreFrame frame s index cardinality).contract = frame.contract ∧
    (swapWriteStoreFrame frame s index cardinality).immutables = frame.immutables := by
  dsimp only [swapWriteStoreFrame, swapWriteIndexTempFrame, swapWriteTickFrame,
    swapWritePriceFrame, swapWriteCardinalityFrame, swapWriteIndexFrame]
  exact ⟨rfl, rfl⟩

theorem swapWriteStoreFrame_get (frame : Frame) (s : SwapStateData)
    (index cardinality : UInt256) (name : Ident)
    (hn : name ∉ ["observationIndex", "observationCardinality", "__t17", "__t18", "__t19",
      "__t20"]) :
    (swapWriteStoreFrame frame s index cardinality).locals.get? name = frame.locals.get? name := by
  simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hn
  rcases hn with ⟨hi, hc, h17, h18, h19, h20⟩
  swap_write_temp_get
  simp only [beq_iff_eq, Ne.symm hi, Ne.symm hc, Ne.symm h17, Ne.symm h18, Ne.symm h19,
    Ne.symm h20, if_false]

theorem swapWriteStoresSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (index cardinality : UInt256) (hf : frame.contract = contract)
    (hs : frame.locals.get? "state" = some s.value) (hbase : frame.locals.get? "slot0" = none)
    (hr : frame.locals.get? "__c16" = some (.tuple
      [.int (Int.ofNat index.toNat), .int (Int.ofNat cardinality.toNat)])) :
    ExecBlock config frame evm (swapWriteBody.drop 1)
      (.ok (swapWriteStoreFrame frame s index cardinality)
        (swapSlotFieldsState evm s.price (EVM.wordOfInt s.tick) index cardinality)) := by
  have h1 : ExecStmt config frame evm swapWriteBody[1]!
      (.ok (swapWriteIndexFrame frame index) evm) :=
    ExecStmt.letDecl (evalExpr_tupleGet (evalExpr_var_get hr) rfl)
  have hr1 : (swapWriteIndexFrame frame index).locals.get? "__c16" = some (.tuple
      [.int (Int.ofNat index.toNat), .int (Int.ofNat cardinality.toNat)]) := by
    swap_write_temp_get
    exact hr
  have h2 : ExecStmt config (swapWriteIndexFrame frame index) evm swapWriteBody[2]!
      (.ok (swapWriteCardinalityFrame frame index cardinality) evm) :=
    ExecStmt.letDecl (evalExpr_tupleGet (evalExpr_var_get hr1) rfl)
  have hs2 : (swapWriteCardinalityFrame frame index cardinality).locals.get? "state" =
      some s.value := by swap_write_temp_get; exact hs
  have h3 : ExecStmt config (swapWriteCardinalityFrame frame index cardinality) evm
      swapWriteBody[3]! (.ok (swapWritePriceFrame frame s index cardinality) evm) :=
    ExecStmt.letDecl
      (evalExpr_structField (name := "sqrtPriceX96") (evalExpr_var_get hs2) rfl)
  have hs3 : (swapWritePriceFrame frame s index cardinality).locals.get? "state" =
      some s.value := by swap_write_temp_get; exact hs
  have h4 : ExecStmt config (swapWritePriceFrame frame s index cardinality) evm
      swapWriteBody[4]! (.ok (swapWriteTickFrame frame s index cardinality) evm) :=
    ExecStmt.letDecl (evalExpr_structField (name := "tick") (evalExpr_var_get hs3) rfl)
  have hi4 : (swapWriteTickFrame frame s index cardinality).locals.get? "observationIndex" =
      some (.int (Int.ofNat index.toNat)) := by swap_write_temp_get
  have h5 : ExecStmt config (swapWriteTickFrame frame s index cardinality) evm
      swapWriteBody[5]! (.ok (swapWriteIndexTempFrame frame s index cardinality) evm) :=
    ExecStmt.letDecl (evalExpr_var_get hi4)
  have hc5 : (swapWriteIndexTempFrame frame s index cardinality).locals.get?
      "observationCardinality" = some (.int (Int.ofNat cardinality.toNat)) := by
    swap_write_temp_get
  have h6 : ExecStmt config (swapWriteIndexTempFrame frame s index cardinality) evm
      swapWriteBody[6]! (.ok (swapWriteStoreFrame frame s index cardinality) evm) :=
    ExecStmt.letDecl (evalExpr_var_get hc5)
  have hframe := (swapWriteStoreFrame_parts frame s index cardinality).1.trans hf
  have hb := (swapWriteStoreFrame_get frame s index cardinality "slot0" (by decide)).trans hbase
  have hprice : (swapWriteStoreFrame frame s index cardinality).locals.get? "__t17" =
      some (.int (Int.ofNat s.price.toNat)) := by swap_write_temp_get
  have htick : (swapWriteStoreFrame frame s index cardinality).locals.get? "__t18" =
      some (.int s.tick) := by swap_write_temp_get
  have hindex : (swapWriteStoreFrame frame s index cardinality).locals.get? "__t19" =
      some (.int (Int.ofNat index.toNat)) := by swap_write_temp_get
  have hcard : (swapWriteStoreFrame frame s index cardinality).locals.get? "__t20" =
      some (.int (Int.ofNat cardinality.toNat)) := by swap_write_temp_get
  have h7 : ExecStmt config (swapWriteStoreFrame frame s index cardinality) evm
      swapWriteBody[7]!
      (.ok (swapWriteStoreFrame frame s index cardinality) (swapSlotFieldState evm false s.price))
        :=
    ExecStmt.assign (evalExpr_var_get hprice) (by
      simpa only [wordOfInt_ofNat_toNat] using
        assignSwapSlotField_frame evm false (Int.ofNat s.price.toNat) hframe hb)
  have h8 := ExecStmt.assign (evalExpr_var_get (cfg := config)
    (evm := swapSlotFieldState evm false s.price) htick)
    (assignSwapSlotField_frame _ true s.tick hframe hb)
  have h9 := ExecStmt.assign (evalExpr_var_get (cfg := config)
    (evm := swapSlotFieldState (swapSlotFieldState evm false s.price) true (EVM.wordOfInt s.tick))
    hindex) (assignSlot0ObservationField_frame _ false index hframe hb)
  have h10 := ExecStmt.assign (evalExpr_var_get (cfg := config)
    (evm := storeSlot0ObservationField
      (swapSlotFieldState (swapSlotFieldState evm false s.price) true (EVM.wordOfInt s.tick))
      false index) hcard) (assignSlot0ObservationField_frame _ true cardinality hframe hb)
  exact ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consNormal h3
    (ExecBlock.consNormal h4 (ExecBlock.consNormal h5 (ExecBlock.consNormal h6
      (ExecBlock.consNormal h7 (ExecBlock.consNormal h8 (ExecBlock.consNormal h9
        (ExecBlock.consNormal h10 .nil)))))))))

end Benchmarks.UniswapV3.Pool
