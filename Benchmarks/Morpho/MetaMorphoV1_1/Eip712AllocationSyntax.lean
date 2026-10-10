import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSyntax

/-! Cursor accounting for the two domain strings and the empty extensions array. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def domainStringAllocation (version : Bool) (cursor : Expr) (value ret : Ident) : Stmt :=
  .ite (.binary .eq (.immutable (if version then "_version" else "_name")) (.intLit 255))
    [.internalCall allocateFunction.name
      [cursor, .binary .add (.arrayLength .localVar ⟨value, []⟩) (.intLit 32)] ret]
    [.internalCall allocateFunction.name [cursor, .intLit 64] ret]

def allocatedEip712DomainTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[40]!
  { source with
    body := source.body.take 11 ++
      [domainStringAllocation false (.intLit 128) "__c0" "__solcNameEnd",
       .internalCall "_EIP712Version" [] "__c1",
       domainStringAllocation true (.var "__solcNameEnd") "__c1" "__solcVersionEnd",
       .internalCall allocateFunction.name [.var "__solcVersionEnd", .intLit 32]
         "__solcExtensionsEnd"] ++ source.body.drop 12 }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
