import Benchmarks.UniswapV3Pool.Spec
import Solm.Notation

/-!
# UniswapV3Pool spec through the Solm syntax-facing module

This benchmark is large enough that the current notation frontend does not cover the full surface.
The file still mirrors the established benchmark convention by exposing a syntax-side contract value
and checking it is definitionally equal to the AST spec.
-/

open Solm Solm.Notation

namespace Benchmarks.UniswapV3Pool.Syntax

def storageDeclsSyntax : List StorageDecl := Benchmarks.UniswapV3Pool.storageDecls

def constructorDeclSyntax : ConstructorDecl := Benchmarks.UniswapV3Pool.constructorDecl

def transitionsSyntax : List TransitionDecl := Benchmarks.UniswapV3Pool.transitions

def contractSyntax : ContractDecl :=
  { name := "UniswapV3Pool"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    structs := Benchmarks.UniswapV3Pool.structs
    functions := []
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.UniswapV3Pool.storageDecls := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.UniswapV3Pool.contract := by
  rfl

end Benchmarks.UniswapV3Pool.Syntax
