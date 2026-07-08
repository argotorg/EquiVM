import Benchmarks.Dss.Flopper.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Flopper spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Flopper.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.Flopper.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Flopper.contract := by
  rfl

end Benchmarks.Dss.Flopper.Syntax
