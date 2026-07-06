import Benchmarks.UniswapV3Pool.Spec
import Solm.Notation

/-!
# UniswapV3Pool spec through the Solm syntax-facing module

This benchmark is large enough that the current notation frontend does not cover the full surface.
The file still mirrors the established benchmark convention by exposing a syntax-side contract value
and checking it is definitionally equal to the AST spec.
-/

open Solm Solm.Notation Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool.Syntax

def storageDeclsSyntax : List StorageDecl := Benchmarks.UniswapV3Pool.storageDecls

def constructorDeclSyntax : ConstructorDecl := Benchmarks.UniswapV3Pool.constructorDecl

def transitionsSyntax (v : PoolImmutables) : List TransitionDecl :=
  Benchmarks.UniswapV3Pool.transitions v

def functionsSyntax (v : PoolImmutables) : List FunctionDecl :=
  Benchmarks.UniswapV3Pool.functions v

def contractSyntax (v : PoolImmutables) : ContractDecl :=
  { name := "UniswapV3Pool"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    structs := Benchmarks.UniswapV3Pool.structs
    functions := functionsSyntax v
    transitions := transitionsSyntax v }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.UniswapV3Pool.storageDecls := by
  rfl

theorem contractSyntax_eq (v : PoolImmutables) :
    contractSyntax v = Benchmarks.UniswapV3Pool.contract v := by
  rfl

end Benchmarks.UniswapV3Pool.Syntax
