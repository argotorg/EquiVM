import Benchmarks.Dss.Cat.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Cat spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Cat.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.Cat.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Cat.contract := by
  rfl

end Benchmarks.Dss.Cat.Syntax
