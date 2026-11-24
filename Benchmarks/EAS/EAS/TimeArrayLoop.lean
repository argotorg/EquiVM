import Benchmarks.EAS.EAS.TimeArray
import Benchmarks.EAS.EAS.WhileInvariant

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

/-- The EVM cursor shared by the two word-array time loops. -/
def TimeArrayRun (fork : Ethereum.Fork) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (pc start time : UInt256) (R : List UInt256) (rdata : ByteArray) (length i : Nat) (evm : EVM.State) : Prop :=
  ∃ mem aw k C, RD fork code ee g s0 pc
    (UInt256.ofNat i :: UInt256.ofNat length :: start :: time :: R) mem aw rdata evm.accountMap k C

theorem timeArrayLoop_correct {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc start time : UInt256} {R : List UInt256} {rdata : ByteArray} {imms : Store}
    {words : List UInt256} {heap : Nat} {body : Body}
    (hstep : ∀ i locals evm, i < words.length → TimeArrayInv locals words time heap i → evm.executionEnv = ee →
      TimeArrayRun fork code ee g s0 pc start time R rdata words.length i evm →
      (∃ locals' evm',
        ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm body
          (.ok {contract := contract, locals := locals', immutables := imms} evm') ∧
        TimeArrayInv locals' words time heap (i + 1) ∧ evm'.executionEnv = ee ∧
        TimeArrayRun fork code ee g s0 pc start time R rdata words.length (i + 1) evm') ∨
      (ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm body .reverted ∧ RDrev fork code g s0) ∨
      (ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm body .staticViolation ∧ RDstatic fork code g s0))
    (hend : ∀ evm, TimeArrayRun fork code ee g s0 pc start time R rdata words.length words.length evm →
      RDret fork code g s0 evm.accountMap time.toByteArray) :
    ∀ n i locals evm, i + n = words.length → TimeArrayInv locals words time heap i → evm.executionEnv = ee →
      TimeArrayRun fork code ee g s0 pc start time R rdata words.length i evm →
      (∃ locals' evm',
        ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm (.while timeArrayGuard body)
          (.ok {contract := contract, locals := locals', immutables := imms} evm') ∧
        TimeArrayInv locals' words time heap words.length ∧ RDret fork code g s0 evm'.accountMap time.toByteArray) ∨
      (ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm (.while timeArrayGuard body) .reverted ∧ RDrev fork code g s0) ∨
      (ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm (.while timeArrayGuard body) .staticViolation ∧ RDstatic fork code g s0) := by
  let inv := fun i locals evm => TimeArrayInv locals words time heap i ∧ evm.executionEnv = ee ∧
    TimeArrayRun fork code ee g s0 pc start time R rdata words.length i evm
  let post := fun (locals : Store) (evm : EVM.State) => TimeArrayInv locals words time heap words.length ∧ RDret fork code g s0 evm.accountMap time.toByteArray
  have hr := execWhile_invariant (cfg := config) (contract := contract) (imms := imms)
    (cond := timeArrayGuard) (body := body) (bound := words.length) inv post (RDrev fork code g s0) (RDstatic fork code g s0)
    (fun _ _ _ _ h => timeArrayGuard_eval h.1)
    (fun locals evm h => ⟨h.1, hend evm h.2.2⟩)
    (fun i locals evm hi h => hstep i locals evm hi h.1 h.2.1 h.2.2)
  intro n i locals evm hn h heen hrun
  exact hr n i locals evm hn ⟨h, heen, hrun⟩

end Benchmarks.EAS.EAS
