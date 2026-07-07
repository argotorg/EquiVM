import Benchmarks.Dss.Flipper.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Flipper spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Flipper.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.Flipper.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Flipper.contract := by
  rfl

end Benchmarks.Dss.Flipper.Syntax
