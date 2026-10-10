import Benchmarks.UniswapV4PoolManager.TickLogSource
import Benchmarks.UniswapV4PoolManager.TransientSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

structure TickLogStage where
  name : Ident
  bit : Nat
  normalize : Bool

def TickLogStage.valid (stage : TickLogStage) : Prop :=
  stage.bit < 256 ∧ stage.name ≠ "r" ∧ stage.name ≠ "log_2"

instance (stage : TickLogStage) : Decidable stage.valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def TickLogStage.statements (stage : TickLogStage) : List Stmt :=
  [.internalCall "TickMath_logStep" [.var "r", .var "log_2", .intLit (Int.ofNat stage.bit), .boolLit stage.normalize] stage.name,
   .assign .localVar {base := "r"} (.tupleGet (.var stage.name) 0),
   .assign .localVar {base := "log_2"} (.tupleGet (.var stage.name) 1)]

def tickLogStages (r log2 : UInt256) : List TickLogStage → UInt256 × UInt256
  | [] => (r, log2)
  | stage :: rest => tickLogStages (tickLogNext r stage.normalize) (tickLogWord r log2 stage.bit) rest

def tickLogStageData : List TickLogStage :=
  [⟨"logStep0", 63, true⟩, ⟨"logStep1", 62, true⟩, ⟨"logStep2", 61, true⟩,
   ⟨"logStep3", 60, true⟩, ⟨"logStep4", 59, true⟩, ⟨"logStep5", 58, true⟩,
   ⟨"logStep6", 57, true⟩, ⟨"logStep7", 56, true⟩, ⟨"logStep8", 55, true⟩,
   ⟨"logStep9", 54, true⟩, ⟨"logStep10", 53, true⟩, ⟨"logStep11", 52, true⟩,
   ⟨"logStep12", 51, true⟩, ⟨"logStep13", 50, false⟩]

theorem tickLogStageExec {f : Frame} {evm : EVM.State} {r log2 : UInt256}
    (stage : TickLogStage) (hb : stage.bit < 256)
    (hnr : stage.name ≠ "r") (hnl : stage.name ≠ "log_2")
    (hf : f.contract = contract)
    (hr : f.locals.get? "r" = some (.int (Int.ofNat r.toNat)))
    (hl : f.locals.get? "log_2" = some (.int (EVM.signed log2))) :
    ∃ f', ExecBlock config f evm stage.statements (.ok f' evm) ∧
      f'.locals.get? "r" = some (.int (Int.ofNat (tickLogNext r stage.normalize).toNat)) ∧
      f'.locals.get? "log_2" = some (.int (EVM.signed (tickLogWord r log2 stage.bit))) ∧
      f'.contract = f.contract ∧
      ∀ name, name ≠ "r" → name ≠ "log_2" → name ≠ stage.name →
        f'.locals.get? name = f.locals.get? name := by
  let result : List Value := [.int (Int.ofNat (tickLogNext r stage.normalize).toNat),
    .int (EVM.signed (tickLogWord r log2 stage.bit))]
  let f1 : Frame := {f with locals := f.locals.insert stage.name (.tuple result)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "r" (.int (Int.ofNat (tickLogNext r stage.normalize).toNat))}
  let f3 : Frame := {f2 with locals := f2.locals.insert "log_2" (.int (EVM.signed (tickLogWord r log2 stage.bit)))}
  have hc := tickLogCall (evm := evm) hf hb (evalLocalValue hr) (evalLocalValue hl)
    (show evalExpr? config f evm (.intLit (Int.ofNat stage.bit)) = .ok (.int (Int.ofNat stage.bit)) by
      simp only [evalExpr?, pure])
    (show evalExpr? config f evm (.boolLit stage.normalize) = .ok (.bool stage.normalize) by
      simp only [evalExpr?, pure]) stage.name
  have htuple1 : f1.locals.get? stage.name = some (.tuple result) := store_get_self _ _ _
  have hr1 : f1.locals.get? "r" = some (.int (Int.ofNat r.toNat)) :=
    (store_get_ne _ _ (beq_eq_false_iff_ne.mpr hnr)).trans hr
  have hl2 : f2.locals.get? "log_2" = some (.int (EVM.signed log2)) :=
    (store_get_ne2 _ _ _ (beq_eq_false_iff_ne.mpr hnl) (by decide : ("r" == "log_2") = false)).trans hl
  have htuple2 : f2.locals.get? stage.name = some (.tuple result) :=
    (store_get_ne _ _ (beq_eq_false_iff_ne.mpr (Ne.symm hnr))).trans htuple1
  refine ⟨f3, ExecBlock.consNormal hc (ExecBlock.consNormal
    (ExecStmt.assign (evalTupleProjection (evalLocalValue htuple1) rfl) (assignLocalValue hr1))
    (ExecBlock.consNormal (ExecStmt.assign (evalTupleProjection (evalLocalValue htuple2) rfl)
      (assignLocalValue hl2)) ExecBlock.nil)), ?_, store_get_self _ _ _, rfl, ?_⟩
  · exact (store_get_ne _ _ (by decide : ("log_2" == "r") = false)).trans (store_get_self _ _ _)
  · intro name hrn hln hsn
    exact store_get_ne3 _ _ _ _ (beq_eq_false_iff_ne.mpr (Ne.symm hsn))
      (beq_eq_false_iff_ne.mpr (Ne.symm hrn)) (beq_eq_false_iff_ne.mpr (Ne.symm hln))

theorem tickLogStagesExec {f : Frame} {evm : EVM.State} {r log2 : UInt256}
    (stages : List TickLogStage)
    (hv : ∀ stage ∈ stages, stage.valid)
    (hf : f.contract = contract)
    (hr : f.locals.get? "r" = some (.int (Int.ofNat r.toNat)))
    (hl : f.locals.get? "log_2" = some (.int (EVM.signed log2))) :
    ∃ f', ExecBlock config f evm (stages.flatMap TickLogStage.statements) (.ok f' evm) ∧
      f'.locals.get? "r" = some (.int (Int.ofNat (tickLogStages r log2 stages).1.toNat)) ∧
      f'.locals.get? "log_2" = some (.int (EVM.signed (tickLogStages r log2 stages).2)) ∧
      f'.contract = f.contract ∧
      ∀ name, name ≠ "r" → name ≠ "log_2" → (∀ stage ∈ stages, name ≠ stage.name) →
        f'.locals.get? name = f.locals.get? name := by
  induction stages generalizing f r log2 with
  | nil => exact ⟨f, ExecBlock.nil, hr, hl, rfl, fun _ _ _ _ => rfl⟩
  | cons stage rest ih =>
    have hs := hv stage (by simp only [List.mem_cons, true_or])
    obtain ⟨f1, he, hr1, hl1, hc1, hk1⟩ := tickLogStageExec stage hs.1 hs.2.1 hs.2.2 hf hr hl
    obtain ⟨f2, hrest, hr2, hl2, hc2, hk2⟩ := ih
      (fun s hm => hv s (List.mem_cons_of_mem _ hm)) (hc1.trans hf) hr1 hl1
    exact ⟨f2, execBlock_append_ok he hrest, hr2, hl2, hc2.trans hc1,
      fun name hnr hnl hns => (hk2 name hnr hnl (fun s hm => hns s (List.mem_cons_of_mem _ hm))).trans
        (hk1 name hnr hnl (hns stage (by simp only [List.mem_cons, true_or])))⟩

end Benchmarks.UniswapV4PoolManager
