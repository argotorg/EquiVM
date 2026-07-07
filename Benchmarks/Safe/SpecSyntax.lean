import Benchmarks.Safe.Spec
import Solm.Notation

/-!
# Safe spec through the Solm syntax-facing module

This benchmark is large enough that the current notation frontend does not cover the full surface.
The file still mirrors the established benchmark convention by exposing a syntax-side contract value
and checking it is definitionally equal to the AST spec.
-/

open Solm Solm.Notation

namespace Benchmarks.Safe.Syntax

def storageDeclsSyntax : List StorageDecl := Benchmarks.Safe.storageDecls

def constructorDeclSyntax : ConstructorDecl := Benchmarks.Safe.constructorDecl

def transitionsSyntax : List TransitionDecl := Benchmarks.Safe.transitions

def functionsSyntax : List FunctionDecl := Benchmarks.Safe.internalFunctions

def receiveSyntax : TransitionDecl := Benchmarks.Safe.receiveTransition

def fallbackSyntax : TransitionDecl := Benchmarks.Safe.fallbackTransition

def contractSyntax : ContractDecl :=
  { name := "Safe"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    functions := functionsSyntax
    transitions := transitionsSyntax
    receive := some receiveSyntax
    fallback := some fallbackSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.Safe.storageDecls := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.Safe.contract := by
  rfl

end Benchmarks.Safe.Syntax
