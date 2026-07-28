import Benchmarks.Xxx.Bytecode
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Xxx shared proof foundation (TEMPLATE)

Contract-wide selector notation and constants for the optimized runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Xxx

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev xxxSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order (index comments per signature). -/
def xxxSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x55, 0x24, 0x11, 0x0f]⟩  -- setValue(uint256)  TODO real bytes
  | _ => ⟨#[0x3f, 0xa4, 0xf2, 0x45]⟩  -- value()            TODO real bytes

-- TODO: dispatcher pc constants (root split, group splits, first-arm pcs) read off the
-- disassembly, e.g.:
-- def xxxRootSplitPc : UInt256 := ⟨0x4b⟩

end Benchmarks.Xxx
