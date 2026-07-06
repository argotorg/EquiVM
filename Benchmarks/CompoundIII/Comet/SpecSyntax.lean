import Benchmarks.CompoundIII.Comet.Spec
import Solm.Notation

/-!
# Compound III CometWithExtendedAssetList spec through the Solm syntax-facing module

This benchmark is large enough that the current notation frontend does not cover the full surface.
The file still mirrors the established benchmark convention by exposing a syntax-side contract value
and checking it is definitionally equal to the AST spec.
-/

open Solm Solm.Notation Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet.Syntax

def storageDeclsSyntax : List StorageDecl := Benchmarks.CompoundIII.Comet.storageDecls

def constructorDeclSyntax : ConstructorDecl := Benchmarks.CompoundIII.Comet.constructorDecl

def transitionsSyntax (v : CometImmutables) : List TransitionDecl :=
  Benchmarks.CompoundIII.Comet.transitions v

def fallbackTransitionSyntax (v : CometImmutables) : TransitionDecl :=
  Benchmarks.CompoundIII.Comet.fallbackTransition v

def contractSyntax (v : CometImmutables) : ContractDecl :=
  { name := "CometWithExtendedAssetList"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    structs := Benchmarks.CompoundIII.Comet.structs
    functions := []
    transitions := transitionsSyntax v
    fallback := some (fallbackTransitionSyntax v) }

theorem storageDeclsSyntax_eq :
    storageDeclsSyntax = Benchmarks.CompoundIII.Comet.storageDecls := by
  rfl

theorem contractSyntax_eq (v : CometImmutables) :
    contractSyntax v = Benchmarks.CompoundIII.Comet.contract v := by
  rfl

end Benchmarks.CompoundIII.Comet.Syntax
