import Benchmarks.CompoundIII.Comet.SignedPresentValueModel
import Benchmarks.CompoundIII.Comet.PrincipalValueWords
import Benchmarks.CompoundIII.Comet.WithdrawAmountsWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def withdrawBaseBalance (evm : EVM.State) (principal amount : UInt256) : UInt256 :=
  UInt256.sub (signedPresentValueWord evm principal) amount

def withdrawBaseBalanceInt (evm : EVM.State) (principal amount : UInt256) : Int :=
  signedPresentValueInt evm principal - Int.ofNat amount.toNat

def withdrawBasePrincipal (evm : EVM.State) (principal amount : UInt256) : UInt256 :=
  principalValueWord evm (withdrawBaseBalance evm principal amount)

def WithdrawBaseBalanceFits (evm : EVM.State) (principal amount : UInt256) : Prop :=
  -(2^103 : Int) < signed104 principal ∧ amount.toNat < 2^255 ∧
    -(2^255 : Int) ≤ withdrawBaseBalanceInt evm principal amount

def WithdrawBaseMathFits (evm : EVM.State) (principal amount : UInt256) : Prop :=
  WithdrawBaseBalanceFits evm principal amount ∧
    PrincipalValueFits evm (withdrawBaseBalance evm principal amount) ∧
    WithdrawAmountsFits principal (withdrawBasePrincipal evm principal amount)

instance (evm : EVM.State) (principal amount : UInt256) :
    Decidable (WithdrawBaseBalanceFits evm principal amount) := by
  unfold WithdrawBaseBalanceFits; infer_instance

instance (evm : EVM.State) (principal amount : UInt256) :
    Decidable (WithdrawBaseMathFits evm principal amount) := by
  unfold WithdrawBaseMathFits; infer_instance

theorem withdrawBaseBalance_int {evm : EVM.State} {principal amount : UInt256}
    (hf : WithdrawBaseBalanceFits evm principal amount) :
    signedWord (withdrawBaseBalance evm principal amount) =
      withdrawBaseBalanceInt evm principal amount := by
  have hp := signedPresentValueWord_int evm principal hf.1
  have hb := signedWord_bounds (signedPresentValueWord evm principal)
  unfold withdrawBaseBalance withdrawBaseBalanceInt
  rw [signedWord_sub_of_range, hp, signedWord_low hf.2.1]
  · rw [hp, signedWord_low hf.2.1]
    exact hf.2.2
  · rw [hp, signedWord_low hf.2.1]
    rw [hp] at hb
    simp only [Int.ofNat_eq_natCast]
    omega

def withdrawBaseMathBlock : List Stmt :=
  [.internalCall "presentValue" [.var "srcPrincipal"] "__c1",
    .internalCall "signed256" [.var "amount"] "__c2",
    .letDecl "srcBalance" (some (.elem (.int (.sint ⟨256, by decide⟩))))
      (.inRange (.sint ⟨256, by decide⟩)
      (.binary .sub (.var "__c1") (.var "__c2"))),
    .internalCall "principalValue" [.var "srcBalance"] "srcPrincipalNew",
    .internalCall "withdrawAndBorrowAmount" [.var "srcPrincipal", .var "srcPrincipalNew"] "__c4",
    .letDecl "withdrawAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c4") 0),
    .letDecl "borrowAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c4") 1)]

def withdrawBaseMathStack (evm : EVM.State) (principal ptr recipient amount src ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [withdrawBorrowAmount principal (withdrawBasePrincipal evm principal amount),
    withdrawSupplyAmount principal (withdrawBasePrincipal evm principal amount),
    UInt256.ofNat 12598, ptr, withdrawBasePrincipal evm principal amount,
    UInt256.ofNat 15852, withdrawBaseBalance evm principal amount, recipient, amount, src, ret] ++ R

def withdrawBaseMathFrame (frame : Frame) (evm : EVM.State) (principal amount : UInt256) : Frame :=
  let next := withdrawBasePrincipal evm principal amount
  let supplied := withdrawSupplyAmount principal next
  let borrowed := withdrawBorrowAmount principal next
  { frame with
    locals := ((((((frame.locals.insert "__c1" (.int (signedPresentValueInt evm principal))).insert
      "__c2" (.int amount.toNat)).insert "srcBalance"
      (.int (withdrawBaseBalanceInt evm principal amount))).insert "srcPrincipalNew"
      (.int (principalValueInt evm (withdrawBaseBalance evm principal amount)))).insert "__c4"
      (.tuple [.int supplied.toNat, .int borrowed.toNat])).insert "withdrawAmount"
      (.int supplied.toNat)).insert "borrowAmount" (.int borrowed.toNat) }

end Benchmarks.CompoundIII.Comet
