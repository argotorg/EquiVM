import Benchmarks.EAS.EAS.SchemaControl
import Benchmarks.EAS.EAS.Storage
import Benchmarks.EAS.EAS.RuntimeBlocks_034

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def schemaUIDStmt : Stmt := .require (.binary .ne (.field (.var "schemaRecord") "uid")
  (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩)))

theorem schemaUIDSource {cfg : Config} {L imms : Store} {evm : EVM.State} {s : SchemaRecord}
    (hs : L.get? "schemaRecord" = some s.value) :
    if s.uid ≠ ⟨0⟩ then
      ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm schemaUIDStmt
        (.ok {contract := contract,locals := L,immutables := imms} evm)
    else ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm schemaUIDStmt .reverted := by
  have he : evalExpr? cfg {contract := contract,locals := L,immutables := imms} evm
      (.field (.var "schemaRecord") "uid") = .ok (wordBytes32Value s.uid) := by
    simp only [evalExpr?,hs,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  have hc : evalExpr? cfg {contract := contract,locals := L,immutables := imms} evm
      (.binary .ne (.field (.var "schemaRecord") "uid") (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩))) =
      .ok (.bool (decide (s.uid ≠ ⟨0⟩))) := by
    simp only [evalExpr?,he,EvalResult.bind,bind,pure]
    exact evalBytes32Ne _ _
  by_cases hz : s.uid ≠ ⟨0⟩
  · rw [if_pos hz]
    exact ExecStmt.requireTrue (by simpa only [decide_eq_true hz] using hc)
  · rw [if_neg hz]
    exact ExecStmt.requireFalse (by simpa only [decide_eq_false hz] using hc)

def schemaUIDAfterPC : SchemaCallSite → UInt256
  | .at7795 .. => ⟨7819⟩ | .at10016 .. => ⟨10040⟩
  | .at12196 => ⟨12220⟩ | .at12855 => ⟨12879⟩
def schemaUIDStack (site : SchemaCallSite) (record : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .at7795 a b => a::b::record::R
  | .at10016 a b c d e => a::b::c::d::e::record::R
  | .at12196 | .at12855 => record::R

theorem easSchemaUIDCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {record uid : UInt256} {R : List UInt256} (v : EASImmutables) (site : SchemaCallSite)
    (hstack : R.length+8 ≤ 1024) (hu : memLoad record mem = uid)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaDonePC site) (schemaDoneStack v site record R) mem aw rdata σ k C) :
    if uid ≠ ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (schemaUIDAfterPC site) (schemaUIDStack site record R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hz : uid ≠ ⟨0⟩
  · rw [if_pos hz]
    have hc : UInt256.isZero (memLoad record mem) = UInt256.ofNat 0 := by rw [hu,isZero_eq_zero_of_ne hz]; rfl
    cases site with
    | at7795 a b => exact easBlocks.eas_block_7810_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
    | at10016 a b c d e => exact easBlocks.eas_block_10031_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
    | at12196 => exact easBlocks.eas_block_12211_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
    | at12855 => exact easBlocks.eas_block_12870_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd
  · rw [if_neg hz]
    have hc : UInt256.isZero (memLoad record mem) ≠ UInt256.ofNat 0 := by rw [hu,not_ne_iff.mp hz]; decide
    have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 9765) = true := by rw [easPatchedValidJumps v]; jump_dest
    have hr : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨9765⟩ (schemaUIDStack site record R) mem a rdata σ j D := by
      cases site with
      | at7795 a b => exact easBlocks.eas_block_7810_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc hd rd
      | at10016 a b c d e => exact easBlocks.eas_block_10031_taken_packed (immWords := wordsOf (immStore v)) hstack hc hd rd
      | at12196 => exact easBlocks.eas_block_12211_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc hd rd
      | at12855 => exact easBlocks.eas_block_12870_taken_packed (immWords := wordsOf (immStore v)) (by omega) hc hd rd
    obtain ⟨a,j,D,hr⟩ := hr
    exact easBlocks.eas_block_9765 (immWords := wordsOf (immStore v))
      (by cases site <;> simp only [schemaUIDStack,List.length_cons] <;> omega) hr

end Benchmarks.EAS.EAS
