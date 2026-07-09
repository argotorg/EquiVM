import Benchmarks.Dss.End.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS End spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.End.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.End.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.End.contract := by
  rfl

end Benchmarks.Dss.End.Syntax
