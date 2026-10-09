import Benchmarks.CompoundIII.Comet.SignedArithmeticWords
import Benchmarks.CompoundIII.Comet.Spec

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def principalDecrease (old next : UInt256) : UInt256 :=
  UInt256.ofNat (signed104 old - signed104 next).toNat

theorem principalDecrease_toNat (old next : UInt256) :
    (principalDecrease old next).toNat = (signed104 old - signed104 next).toNat := by
  apply UInt256.toNat_ofNat_of_lt
  have ho := signed104_bounds old
  have hn := signed104_bounds next
  change (signed104 old - signed104 next).toNat < 2^256
  omega

theorem principalDecrease_lt (old next : UInt256) :
    (principalDecrease old next).toNat < 2^104 := by
  rw [principalDecrease_toNat]
  have ho := signed104_bounds old
  have hn := signed104_bounds next
  omega

theorem principalDecrease_int {old next : UInt256} (hle : signed104 next ≤ signed104 old) :
    Int.ofNat (principalDecrease old next).toNat = signed104 old - signed104 next := by
  rw [principalDecrease_toNat]
  exact Int.toNat_of_nonneg (by omega)

theorem principalDecrease_word {old next : UInt256} (hle : signed104 next ≤ signed104 old) :
    UInt256.sub (UInt256.signextend (UInt256.ofNat 12) old)
      (UInt256.signextend (UInt256.ofNat 12) next) = principalDecrease old next := by
  rw [← signedWord_encode (UInt256.sub _ _), signed104_sub_word,
    ← principalDecrease_int hle, wordOfInt_ofNat_toNat]

def withdrawSupplyAmount (old next : UInt256) : UInt256 :=
  if signed104 old < signed104 next then ⟨0⟩ else
  if 0 ≤ signed104 next then principalDecrease old next else
  if signed104 old ≤ 0 then ⟨0⟩ else positivePrincipal old

def withdrawBorrowAmount (old next : UInt256) : UInt256 :=
  if signed104 old < signed104 next then ⟨0⟩ else
  if 0 ≤ signed104 next then ⟨0⟩ else
  if signed104 old ≤ 0 then principalDecrease old next else negativePrincipal next

def WithdrawAmountsFits (old next : UInt256) : Prop :=
  if signed104 old < signed104 next then True else
  if 0 ≤ signed104 next then signed104 old - signed104 next < (2^103 : Int) else
  if signed104 old ≤ 0 then signed104 old - signed104 next < (2^103 : Int) else
    -(2^103 : Int) < signed104 next

instance (priority := low) (old next : UInt256) : Decidable (WithdrawAmountsFits old next) := by
  unfold WithdrawAmountsFits
  infer_instance

def withdrawAmountsDiffExpr : Expr :=
  .cast (.inRange (.sint ⟨104, by decide⟩)
    (.binary .sub (.var "oldPrincipal") (.var "newPrincipal")))
    (.elem (.int (.uint ⟨104, by decide⟩)))

def withdrawAmountsCallable : CallableDecl :=
  { params := [⟨"oldPrincipal", .elem (.int (.sint ⟨104, by decide⟩))⟩,
      ⟨"newPrincipal", .elem (.int (.sint ⟨104, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨104, by decide⟩)),
      .elem (.int (.uint ⟨104, by decide⟩))]
    body := [.ite (.binary .gt (.var "newPrincipal") (.var "oldPrincipal"))
        [.return [.intLit 0, .intLit 0]] [],
      .ite (.binary .ge (.var "newPrincipal") (.intLit 0))
        [.return [withdrawAmountsDiffExpr, .intLit 0]]
        [.ite (.binary .le (.var "oldPrincipal") (.intLit 0))
          [.return [.intLit 0, withdrawAmountsDiffExpr]]
          [.return [.cast (.var "oldPrincipal") (.elem (.int (.uint ⟨104, by decide⟩))),
            .cast (.inRange (.sint ⟨104, by decide⟩)
              (.binary .sub (.intLit 0) (.var "newPrincipal")))
              (.elem (.int (.uint ⟨104, by decide⟩)))]]]] }

theorem withdrawAmountsCallable_lookup :
    lookupCallable? contract "withdrawAndBorrowAmount" = some withdrawAmountsCallable := rfl

def withdrawAmountsEntry (imms : Store) (old next : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "newPrincipal" (.int (signed104 next))).insert
      "oldPrincipal" (.int (signed104 old)) }

end Benchmarks.CompoundIII.Comet
