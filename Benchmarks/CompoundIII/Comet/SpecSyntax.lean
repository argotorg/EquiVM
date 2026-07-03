import Benchmarks.CompoundIII.Comet.Spec
import Solm.Notation

/-!
# Compound III CometWithExtendedAssetList spec through the Solm syntax-facing module

This benchmark is large enough that the current notation frontend does not cover the full surface.
The file still mirrors the established benchmark convention by exposing a syntax-side contract value
and checking it is definitionally equal to the AST spec.
-/

open Solm Solm.Notation

namespace Benchmarks.CompoundIII.Comet.Syntax

def storageDeclsSyntax : List StorageDecl := Benchmarks.CompoundIII.Comet.storageDecls

def constructorDeclSyntax : ConstructorDecl := Benchmarks.CompoundIII.Comet.constructorDecl

def transitionsSyntax : List TransitionDecl := Benchmarks.CompoundIII.Comet.transitions

def fallbackTransitionSyntax : TransitionDecl := Benchmarks.CompoundIII.Comet.fallbackTransition

def contractSyntax : ContractDecl :=
  { name := "CometWithExtendedAssetList"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    structs := Benchmarks.CompoundIII.Comet.structs
    functions := []
    transitions := transitionsSyntax
    fallback := some fallbackTransitionSyntax }

theorem storageDeclsSyntax_eq :
    storageDeclsSyntax = Benchmarks.CompoundIII.Comet.storageDecls := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.CompoundIII.Comet.contract := by
  rfl

end Benchmarks.CompoundIII.Comet.Syntax
