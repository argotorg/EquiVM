import Benchmarks.Dss.Dog.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Dog spec through the Solm notation frontend

The main spec lives in `Spec.lean`; this companion keeps the benchmark's notation-side check wired
up as the body surface grows.
-/

open Solm Solm.Notation
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog.Syntax

def contractSyntax (v : DogImmutables) : ContractDecl := Benchmarks.Dss.Dog.contract v

theorem contractSyntax_eq (v : DogImmutables) :
    contractSyntax v = Benchmarks.Dss.Dog.contract v := by
  rfl

end Benchmarks.Dss.Dog.Syntax
