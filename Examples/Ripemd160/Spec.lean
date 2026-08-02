import Examples.Ripemd160.SpecSyntax
import Solm.Semantics

/-!
# RIPEMD-160 specification assembly

`SpecSyntax.lean` is the single authored Solm specification. This module supplies stable names
and the empty-layout configuration consumed by the runtime-equivalence scaffold.
-/

open Solm ABI

namespace Ripemd160

def contract : ContractDecl := Syntax.contractSyntax

abbrev fallbackTransition : TransitionDecl := contract.fallback.get!

def storageLayout : StorageLayout where
  layout := fun _ _ => none

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := fun _ _ => none }

end Ripemd160
