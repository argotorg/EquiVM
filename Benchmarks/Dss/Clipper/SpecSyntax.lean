import Benchmarks.Dss.Clipper.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Clipper spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper.Syntax

def contractSyntax (v : ClipperImmutables) : ContractDecl := Benchmarks.Dss.Clipper.contract v

theorem contractSyntax_eq (v : ClipperImmutables) :
    contractSyntax v = Benchmarks.Dss.Clipper.contract v := by
  rfl

end Benchmarks.Dss.Clipper.Syntax
