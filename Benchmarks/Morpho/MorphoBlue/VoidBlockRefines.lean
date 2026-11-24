import Benchmarks.Morpho.MorphoBlue.StateBlock
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: a source suffix and bytecode agree on revert or void completion.
inductive VoidBlockRefines (fork : Ethereum.Fork) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (frame : Frame) (evm : EVM.State) (stmts : List Stmt) : Prop where
  | reverted : ExecBlock fork cfg frame evm stmts .reverted → RDrev fork code g s0 →
      VoidBlockRefines fork cfg code ee g s0 frame evm stmts
  | static : ExecBlock fork cfg frame evm stmts .staticViolation → RDstatic fork code g s0 →
      VoidBlockRefines fork cfg code ee g s0 frame evm stmts
  | ok {frame' evm' σ'} : ExecBlock fork cfg frame evm stmts (.ok frame' evm') →
      SourceState s0 ee σ' evm' → RDret fork code g s0 σ' ByteArray.empty →
      VoidBlockRefines fork cfg code ee g s0 frame evm stmts

theorem VoidBlockRefines.prepend {cfg code ee g s0 frame evm stmts frame₀ evm₀ stmts₀}
    (h : VoidBlockRefines fork cfg code ee g s0 frame evm stmts)
    (hab : StateBlock fork cfg frame₀ evm₀ stmts₀ frame evm stmts) :
    VoidBlockRefines fork cfg code ee g s0 frame₀ evm₀ stmts₀ := by
  cases h with
  | reverted he hr => exact .reverted (hab.run he) hr
  | static he hr => exact .static (hab.run he) hr
  | ok he hs hr => exact .ok (hab.run he) hs hr

end Benchmarks.Morpho.MorphoBlue
