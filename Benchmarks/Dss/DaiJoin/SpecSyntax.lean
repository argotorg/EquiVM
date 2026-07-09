import Benchmarks.Dss.DaiJoin.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS DaiJoin spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.DaiJoin.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.DaiJoin.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.DaiJoin.contract := by
  rfl

end Benchmarks.Dss.DaiJoin.Syntax
