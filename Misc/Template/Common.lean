import Benchmarks.Xxx.Bytecode
import Benchmarks.Xxx.Selectors
import Reasoning.ABI
import Reasoning.Constructor
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Xxx proof prelude (TEMPLATE)

The single import point for contract proof files. It re-exports the contract specification,
bytecode, selector interface, and shared reasoning libraries. Contract-specific definitions or
theorems used by multiple proof files may also live here.
-/
