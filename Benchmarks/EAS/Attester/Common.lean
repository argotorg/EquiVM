import Benchmarks.EAS.Attester.Selectors
import Benchmarks.EAS.Attester.Blocks
import Reasoning.ABI
import Reasoning.Constructor
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody

/-!
# Attester proof prelude

Import point for the specification, patched bytecode, selectors, generated block summaries,
and shared refinement machinery. Functional proof obligations remain unproved.
`Audit.lean` is executable regression evidence and is deliberately separate from this prelude.
-/
