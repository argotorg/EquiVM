import Benchmarks.CompoundIII.Comet.SafeUintSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def principalMagnitudeProduct (present : UInt256) : UInt256 :=
  UInt256.mul present ⟨1000000000000000⟩

def principalMagnitudeSum (index present : UInt256) : UInt256 :=
  principalMagnitudeProduct present + index

def principalMagnitudeNumerator (borrow : Bool) (index present : UInt256) : UInt256 :=
  if borrow then UInt256.sub (principalMagnitudeSum index present) ⟨1⟩
  else principalMagnitudeProduct present

def principalMagnitudeWord (borrow : Bool) (index present : UInt256) : UInt256 :=
  UInt256.div (principalMagnitudeNumerator borrow index present) index

def PrincipalMagnitudeEvalFits (borrow : Bool) (index present : UInt256) : Prop :=
  present.toNat * 1000000000000000 < UInt256.size ∧
    (borrow = true → (principalMagnitudeProduct present).toNat + index.toNat < UInt256.size ∧
      1 ≤ (principalMagnitudeSum index present).toNat) ∧
    index ≠ ⟨0⟩

def PrincipalMagnitudeFits (borrow : Bool) (index present : UInt256) : Prop :=
  PrincipalMagnitudeEvalFits borrow index present ∧
    (principalMagnitudeWord borrow index present).toNat < 2^104

instance (borrow : Bool) (index present : UInt256) :
    Decidable (PrincipalMagnitudeEvalFits borrow index present) := by
  unfold PrincipalMagnitudeEvalFits
  infer_instance

instance (borrow : Bool) (index present : UInt256) :
    Decidable (PrincipalMagnitudeFits borrow index present) := by
  unfold PrincipalMagnitudeFits
  infer_instance

def principalMagnitudeIndexName (borrow : Bool) : Ident :=
  if borrow then "baseBorrowIndex_" else "baseSupplyIndex_"

def principalMagnitudeName (borrow : Bool) : Ident :=
  if borrow then "principalValueBorrow" else "principalValueSupply"

def principalMagnitudeProductExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "presentValue_")
    (.intLit 1000000000000000))

def principalMagnitudeNumeratorExpr (borrow : Bool) : Expr :=
  if borrow then .inRange (.uint ⟨256, by decide⟩)
    (.binary .sub (.inRange (.uint ⟨256, by decide⟩)
      (.binary .add principalMagnitudeProductExpr (.var (principalMagnitudeIndexName borrow))))
      (.intLit 1))
  else principalMagnitudeProductExpr

def principalMagnitudeExpr (borrow : Bool) : Expr :=
  .binary .div (principalMagnitudeNumeratorExpr borrow) (.var (principalMagnitudeIndexName borrow))

def principalMagnitudeCallable (borrow : Bool) : CallableDecl :=
  { params := [⟨principalMagnitudeIndexName borrow, .elem (.int (.uint ⟨64, by decide⟩))⟩,
      ⟨"presentValue_", abiUInt256⟩]
    returnType := [.elem (.int (.uint ⟨104, by decide⟩))]
    body := [.internalCall "safe104" [principalMagnitudeExpr borrow] "__c0",
      .return [.var "__c0"]] }

theorem principalMagnitudeCallable_lookup (borrow : Bool) :
    lookupCallable? contract (principalMagnitudeName borrow) =
      some (principalMagnitudeCallable borrow) := by cases borrow <;> rfl

def principalMagnitudeEntry (imms : Store) (borrow : Bool) (index present : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store) |>.insert "presentValue_" (.int present.toNat)
      |>.insert (principalMagnitudeIndexName borrow) (.int index.toNat) }

end Benchmarks.CompoundIII.Comet
