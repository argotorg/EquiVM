import Benchmarks.Dss.Flapper.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Flapper spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Flapper.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.Flapper.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Flapper.contract := by
  rfl

end Benchmarks.Dss.Flapper.Syntax
