import Benchmarks.Dss.Cure.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Cure spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Cure.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.Cure.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Cure.contract := by
  rfl

end Benchmarks.Dss.Cure.Syntax
