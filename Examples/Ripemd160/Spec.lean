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

abbrev f0Function : FunctionDecl := contract.functions[0]!
abbrev f1Function : FunctionDecl := contract.functions[1]!
abbrev f2Function : FunctionDecl := contract.functions[2]!
abbrev f3Function : FunctionDecl := contract.functions[3]!
abbrev f4Function : FunctionDecl := contract.functions[4]!
abbrev rotl32Function : FunctionDecl := contract.functions[5]!
abbrev wordRowLFunction : FunctionDecl := contract.functions[6]!
abbrev rotRowLFunction : FunctionDecl := contract.functions[7]!
abbrev wordRowRFunction : FunctionDecl := contract.functions[8]!
abbrev rotRowRFunction : FunctionDecl := contract.functions[9]!
abbrev nibbleFunction : FunctionDecl := contract.functions[10]!
abbrev paddedByteFunction : FunctionDecl := contract.functions[11]!
abbrev swap32Function : FunctionDecl := contract.functions[12]!
abbrev hashFunction : FunctionDecl := contract.functions[13]!
abbrev fallbackTransition : TransitionDecl := contract.fallback.get!

def storageLayout : StorageLayout where
  layout := fun _ _ => none

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := fun _ _ => none }

end Ripemd160
