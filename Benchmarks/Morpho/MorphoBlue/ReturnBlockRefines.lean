import Benchmarks.Morpho.MorphoBlue.StateBlock
import Benchmarks.Morpho.MorphoBlue.WordBufferCommon
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: refinement of a source suffix that returns ABI values.
inductive ReturnBlockRefines (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (frame : Frame) (evm : EVM.State) (stmts : List Stmt) (types : List ABIType) : Prop where
  | reverted : ExecBlock cfg frame evm stmts .reverted → RDrev code g s0 →
      ReturnBlockRefines cfg code ee g s0 frame evm stmts types
  | static : ExecBlock cfg frame evm stmts .staticViolation → RDstatic code g s0 →
      ReturnBlockRefines cfg code ee g s0 frame evm stmts types
  | ok {frame' evm' σ' vals bytes} : ExecBlock cfg frame evm stmts (.returned frame' evm' (some vals)) →
      SourceState s0 ee σ' evm' → encodeReturnValues? types vals = some bytes → RDret code g s0 σ' bytes →
      ReturnBlockRefines cfg code ee g s0 frame evm stmts types

theorem ReturnBlockRefines.prepend {cfg code ee g s0 frame evm stmts types frame₀ evm₀ stmts₀}
    (h : ReturnBlockRefines cfg code ee g s0 frame evm stmts types)
    (hab : StateBlock cfg frame₀ evm₀ stmts₀ frame evm stmts) :
    ReturnBlockRefines cfg code ee g s0 frame₀ evm₀ stmts₀ types := by
  cases h with
  | reverted he hr => exact .reverted (hab.run he) hr
  | static he hr => exact .static (hab.run he) hr
  | ok he hs hec hr => exact .ok (hab.run he) hs hec hr

-- LIBRARY CANDIDATE: the common pair of full-width unsigned return values.
theorem uint256PairReturnEncoding (x y : UInt256) :
    encodeReturnValues? [abiUInt256, abiUInt256] [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (returnWordBytes [x, y]) := by
  apply elementaryWordsReturnEncoding
    [(.int abiUInt256Int, .int (Int.ofNat x.toNat), x), (.int abiUInt256Int, .int (Int.ofNat y.toNat), y)]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact encodeABIValue_uint256 _

end Benchmarks.Morpho.MorphoBlue
