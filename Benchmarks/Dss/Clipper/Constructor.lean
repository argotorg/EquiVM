import Benchmarks.Dss.Clipper.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Clipper constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperConstructorCorrect (v : ClipperImmutables) :
    constructorEquivalenceWith (config v) clipperCreationBytecode (contract v)
      (runtimeCodeOf clipperBytecode) := by
  sorry

end Benchmarks.Dss.Clipper
