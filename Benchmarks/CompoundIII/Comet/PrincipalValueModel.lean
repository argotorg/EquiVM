import Benchmarks.CompoundIII.Comet.PrincipalMagnitudeModel
import Benchmarks.CompoundIII.Comet.SignedWord
import Benchmarks.CompoundIII.Comet.TotalsStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def principalValueIndex (evm : EVM.State) (borrow : Bool) : UInt256 :=
  totalsIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) borrow

def principalValueAmount (present : UInt256) (borrow : Bool) : UInt256 :=
  if borrow then UInt256.sub (UInt256.ofNat 0) present else present

def principalValueMagnitude (evm : EVM.State) (present : UInt256) (borrow : Bool) : UInt256 :=
  principalMagnitudeWord borrow (principalValueIndex evm borrow) (principalValueAmount present borrow)

def PrincipalValueBranchFits (evm : EVM.State) (present : UInt256) (borrow : Bool) : Prop :=
  PrincipalMagnitudeFits borrow (principalValueIndex evm borrow) (principalValueAmount present borrow) ∧
    (principalValueMagnitude evm present borrow).toNat < 2^103

def PrincipalValueFits (evm : EVM.State) (present : UInt256) : Prop :=
  -(2^255 : Int) < signedWord present ∧
    PrincipalValueBranchFits evm present (decide (signedWord present < 0))

instance (evm : EVM.State) (present : UInt256) (borrow : Bool) :
    Decidable (PrincipalValueBranchFits evm present borrow) := by
  unfold PrincipalValueBranchFits; infer_instance

instance (evm : EVM.State) (present : UInt256) : Decidable (PrincipalValueFits evm present) := by
  unfold PrincipalValueFits; infer_instance

def principalValueInt (evm : EVM.State) (present : UInt256) : Int :=
  if 0 ≤ signedWord present then Int.ofNat (principalValueMagnitude evm present false).toNat
  else -Int.ofNat (principalValueMagnitude evm present true).toNat

def principalValueWord (evm : EVM.State) (present : UInt256) : UInt256 :=
  if 0 ≤ signedWord present then principalValueMagnitude evm present false
  else UInt256.sub (UInt256.ofNat 0) (principalValueMagnitude evm present true)

def principalValueAmountExpr (borrow : Bool) : Expr :=
  .cast (if borrow then
    .inRange (.sint ⟨256, by decide⟩) (.binary .sub (.intLit 0) (.var "presentValue_"))
    else .var "presentValue_") (.elem (.int (.uint ⟨256, by decide⟩)))

def principalValueReturnExpr (borrow : Bool) : Expr :=
  if borrow then .inRange (.sint ⟨104, by decide⟩) (.binary .sub (.intLit 0) (.var "__c3"))
  else .var "__c1"

def principalValueBranch (borrow : Bool) : List Stmt :=
  [.internalCall (principalMagnitudeName borrow)
      [.storage ⟨totalsIndexName borrow, []⟩, principalValueAmountExpr borrow]
      (if borrow then "__c2" else "__c0"),
    .internalCall "signed104" [.var (if borrow then "__c2" else "__c0")]
      (if borrow then "__c3" else "__c1"),
    .return [principalValueReturnExpr borrow]]

def principalValueCallable : CallableDecl :=
  { params := [⟨"presentValue_", .elem (.int (.sint ⟨256, by decide⟩))⟩]
    returnType := [.elem (.int (.sint ⟨104, by decide⟩))]
    body := [.ite (.binary .ge (.var "presentValue_") (.intLit 0))
      (principalValueBranch false) (principalValueBranch true)] }

theorem principalValueCallable_lookup : lookupCallable? contract "principalValue" =
    some principalValueCallable := rfl

def principalValueEntry (imms : Store) (present : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store).insert "presentValue_" (.int (signedWord present)) }

end Benchmarks.CompoundIII.Comet
