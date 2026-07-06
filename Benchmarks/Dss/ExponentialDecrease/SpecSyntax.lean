import Benchmarks.Dss.ExponentialDecrease.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS ExponentialDecrease spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.ExponentialDecrease.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.ExponentialDecrease.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.ExponentialDecrease.contract := by
  rfl

end Benchmarks.Dss.ExponentialDecrease.Syntax
