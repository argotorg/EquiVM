import Benchmarks.UniswapV2Router02.Spec
import Solm.Notation

/-!
# UniswapV2Router02 spec through the Solm syntax-facing module

This benchmark is large enough that the current notation frontend does not cover the full surface.
The file still mirrors the established benchmark convention by exposing a syntax-side contract value
and checking it is definitionally equal to the AST spec.
-/

open Solm Solm.Notation Benchmarks.UniswapV2Router02.Immutables

namespace Benchmarks.UniswapV2Router02.Syntax

def storageDeclsSyntax : List StorageDecl := Benchmarks.UniswapV2Router02.storageDecls

def constructorDeclSyntax : ConstructorDecl := Benchmarks.UniswapV2Router02.constructorDecl

def functionsSyntax : List FunctionDecl := Benchmarks.UniswapV2Router02.functions

def transitionsSyntax (v : RouterImmutables) : List TransitionDecl :=
  Benchmarks.UniswapV2Router02.transitions v

def receiveTransitionSyntax (v : RouterImmutables) : TransitionDecl :=
  Benchmarks.UniswapV2Router02.receiveTransition v

def contractSyntax (v : RouterImmutables) : ContractDecl :=
  { name := "UniswapV2Router02"
    storage := storageDeclsSyntax
    ctor := constructorDeclSyntax
    functions := functionsSyntax
    transitions := transitionsSyntax v
    receive := some (receiveTransitionSyntax v) }

theorem storageDeclsSyntax_eq :
    storageDeclsSyntax = Benchmarks.UniswapV2Router02.storageDecls := by
  rfl

theorem contractSyntax_eq (v : RouterImmutables) :
    contractSyntax v = Benchmarks.UniswapV2Router02.contract v := by
  rfl

end Benchmarks.UniswapV2Router02.Syntax
