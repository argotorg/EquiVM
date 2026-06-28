import Benchmarks.GnosisMultiSig.Spec
import Solm.Notation

/-!
# Gnosis MultiSigWallet spec through the Solm notation frontend

The current notation frontend does not yet cover dynamic-array storage declarations, dynamic
`bytes`, tuple returns, `for` loops, storage aliases, or low-level calls.  This file still records
the syntax-level fragments that are available today and checks that they desugar to the AST helpers
used by `Benchmarks/GnosisMultiSig/Spec.lean`.
-/

open Solm Solm.Notation

namespace Benchmarks.GnosisMultiSig.Syntax

def nonpayableSyntax : List Stmt :=
  sBlock% {
    require msg.value == 0
  }

theorem nonpayableSyntax_eq : nonpayableSyntax = Benchmarks.GnosisMultiSig.nonpayable := by
  rfl

def requiredTransitionSyntax : TransitionDecl :=
  solm_transition required -> uint256 {
    require msg.value == 0
    return @required
  }

theorem requiredTransitionSyntax_eq :
    requiredTransitionSyntax = Benchmarks.GnosisMultiSig.requiredTransition := by
  rfl

def transactionCountTransitionSyntax : TransitionDecl :=
  solm_transition transactionCount -> uint256 {
    require msg.value == 0
    return @transactionCount
  }

theorem transactionCountTransitionSyntax_eq :
    transactionCountTransitionSyntax = Benchmarks.GnosisMultiSig.transactionCountTransition := by
  rfl

def maxOwnerCountTransitionSyntax : TransitionDecl :=
  solm_transition MAX_OWNER_COUNT -> uint256 {
    require msg.value == 0
    return 50
  }

theorem maxOwnerCountTransitionSyntax_eq :
    maxOwnerCountTransitionSyntax = Benchmarks.GnosisMultiSig.maxOwnerCountTransition := by
  rfl

def contractSyntax : ContractDecl :=
  Benchmarks.GnosisMultiSig.contract

theorem contractSyntax_eq : contractSyntax = Benchmarks.GnosisMultiSig.contract := by
  rfl

end Benchmarks.GnosisMultiSig.Syntax
