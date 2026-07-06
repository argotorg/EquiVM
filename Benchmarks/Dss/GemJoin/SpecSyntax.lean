import Benchmarks.Dss.GemJoin.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS GemJoin spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.GemJoin.Syntax

def contractSyntax : ContractDecl := Benchmarks.Dss.GemJoin.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.GemJoin.contract := by
  rfl

end Benchmarks.Dss.GemJoin.Syntax
