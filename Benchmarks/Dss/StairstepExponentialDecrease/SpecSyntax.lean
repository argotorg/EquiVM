import Benchmarks.Dss.StairstepExponentialDecrease.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS StairstepExponentialDecrease spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.StairstepExponentialDecrease.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.StairstepExponentialDecrease.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.StairstepExponentialDecrease.contract := by
  rfl

end Benchmarks.Dss.StairstepExponentialDecrease.Syntax
