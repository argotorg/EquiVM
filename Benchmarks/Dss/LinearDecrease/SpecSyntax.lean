import Benchmarks.Dss.LinearDecrease.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS LinearDecrease spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.LinearDecrease.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.LinearDecrease.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.LinearDecrease.contract := by
  rfl

end Benchmarks.Dss.LinearDecrease.Syntax
