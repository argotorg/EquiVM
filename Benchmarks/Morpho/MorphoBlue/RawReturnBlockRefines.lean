import Benchmarks.Morpho.MorphoBlue.StateBlock
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

-- GENERALIZES ReturnBlockRefines to source suffixes returning raw bytes.
inductive RawReturnBlockRefines (cfg : Config) (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (frame : Frame) (evm : EVM.State) (stmts : List Stmt) : Prop where
  | reverted : ExecBlock cfg frame evm stmts .reverted → RDrev code g s0 →
      RawReturnBlockRefines cfg code ee g s0 frame evm stmts
  | static : ExecBlock cfg frame evm stmts .staticViolation → RDstatic code g s0 →
      RawReturnBlockRefines cfg code ee g s0 frame evm stmts
  | ok {frame' evm' σ' bytes} :
      ExecBlock cfg frame evm stmts (.returned frame' evm' (some [.bytes bytes])) →
      SourceState s0 ee σ' evm' → RDret code g s0 σ' bytes →
      RawReturnBlockRefines cfg code ee g s0 frame evm stmts

theorem RawReturnBlockRefines.prepend {cfg code ee g s0 frame evm stmts frame₀ evm₀ stmts₀}
    (h : RawReturnBlockRefines cfg code ee g s0 frame evm stmts)
    (hab : StateBlock cfg frame₀ evm₀ stmts₀ frame evm stmts) :
    RawReturnBlockRefines cfg code ee g s0 frame₀ evm₀ stmts₀ := by
  cases h with
  | reverted he hr => exact .reverted (hab.run he) hr
  | static he hr => exact .static (hab.run he) hr
  | ok he hs hr => exact .ok (hab.run he) hs hr

end Benchmarks.Morpho.MorphoBlue
