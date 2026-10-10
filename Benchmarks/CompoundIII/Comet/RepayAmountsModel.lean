import Benchmarks.CompoundIII.Comet.WithdrawAmountsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def repayAmount (old next : UInt256) : UInt256 :=
  if signed104 next < signed104 old then ⟨0⟩ else
  if signed104 next ≤ 0 then principalDecrease next old else
  if 0 ≤ signed104 old then ⟨0⟩ else negativePrincipal old

def supplyAmount (old next : UInt256) : UInt256 :=
  if signed104 next < signed104 old then ⟨0⟩ else
  if signed104 next ≤ 0 then ⟨0⟩ else
  if 0 ≤ signed104 old then principalDecrease next old else positivePrincipal next

def RepayAmountsFits (old next : UInt256) : Prop :=
  if signed104 next < signed104 old then True else
  if signed104 next ≤ 0 then signed104 next - signed104 old < (2^103 : Int) else
  if 0 ≤ signed104 old then signed104 next - signed104 old < (2^103 : Int) else
    -(2^103 : Int) < signed104 old

instance (priority := low) (old next : UInt256) : Decidable (RepayAmountsFits old next) := by
  unfold RepayAmountsFits
  infer_instance

def repayAmountsDiffExpr : Expr :=
  .cast (.inRange (.sint ⟨104, by decide⟩)
    (.binary .sub (.var "newPrincipal") (.var "oldPrincipal")))
    (.elem (.int (.uint ⟨104, by decide⟩)))

def repayAmountsCallable : CallableDecl :=
  { params := [⟨"oldPrincipal", .elem (.int (.sint ⟨104, by decide⟩))⟩,
      ⟨"newPrincipal", .elem (.int (.sint ⟨104, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨104, by decide⟩)),
      .elem (.int (.uint ⟨104, by decide⟩))]
    body := [.ite (.binary .lt (.var "newPrincipal") (.var "oldPrincipal"))
        [.return [.intLit 0, .intLit 0]] [],
      .ite (.binary .le (.var "newPrincipal") (.intLit 0))
        [.return [repayAmountsDiffExpr, .intLit 0]]
        [.ite (.binary .ge (.var "oldPrincipal") (.intLit 0))
          [.return [.intLit 0, repayAmountsDiffExpr]]
          [.return [.cast (.inRange (.sint ⟨104, by decide⟩)
              (.binary .sub (.intLit 0) (.var "oldPrincipal")))
              (.elem (.int (.uint ⟨104, by decide⟩))),
            .cast (.var "newPrincipal") (.elem (.int (.uint ⟨104, by decide⟩)))]]]] }

theorem repayAmountsCallable_lookup :
    lookupCallable? contract "repayAndSupplyAmount" = some repayAmountsCallable := rfl

end Benchmarks.CompoundIII.Comet
