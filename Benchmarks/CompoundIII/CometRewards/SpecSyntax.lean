import Benchmarks.CompoundIII.CometRewards.Spec
import Solm.Notation

/-!
# Compound III CometRewards spec through the Solm syntax-facing module

This benchmark is large enough that the current notation frontend does not cover the full surface.
The file still mirrors the established benchmark convention by exposing a syntax-side contract value
and checking it is definitionally equal to the AST spec.
-/

open Solm Solm.Notation

namespace Benchmarks.CompoundIII.CometRewards.Syntax

def storageDeclsSyntax : List StorageDecl := Benchmarks.CompoundIII.CometRewards.storageDecls

def constructorDeclSyntax : ConstructorDecl := Benchmarks.CompoundIII.CometRewards.constructorDecl

def transitionsSyntax : List TransitionDecl := Benchmarks.CompoundIII.CometRewards.transitions

def functionsSyntax : List FunctionDecl := Benchmarks.CompoundIII.CometRewards.functions

def contractSyntax : ContractDecl :=
  { name := "CometRewards"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    structs := Benchmarks.CompoundIII.CometRewards.structs
    functions := functionsSyntax
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq :
    storageDeclsSyntax = Benchmarks.CompoundIII.CometRewards.storageDecls := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.CompoundIII.CometRewards.contract := by
  rfl

end Benchmarks.CompoundIII.CometRewards.Syntax
