import Benchmarks.CompoundIII.Comet.SignedPresentValueModel
import Benchmarks.CompoundIII.Comet.PrincipalValueWords
import Benchmarks.CompoundIII.Comet.RepayAmountsWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def supplyBaseBalance (evm : EVM.State) (principal amount : UInt256) : UInt256 :=
  signedPresentValueWord evm principal + amount

def supplyBaseBalanceInt (evm : EVM.State) (principal amount : UInt256) : Int :=
  signedPresentValueInt evm principal + Int.ofNat amount.toNat

def supplyBasePrincipal (evm : EVM.State) (principal amount : UInt256) : UInt256 :=
  principalValueWord evm (supplyBaseBalance evm principal amount)

def SupplyBaseBalanceFits (evm : EVM.State) (principal amount : UInt256) : Prop :=
  -(2^103 : Int) < signed104 principal ∧ amount.toNat < 2^255 ∧
    supplyBaseBalanceInt evm principal amount < (2^255 : Int)

def SupplyBaseMathFits (evm : EVM.State) (principal amount : UInt256) : Prop :=
  SupplyBaseBalanceFits evm principal amount ∧
    PrincipalValueFits evm (supplyBaseBalance evm principal amount) ∧
    RepayAmountsFits principal (supplyBasePrincipal evm principal amount)

instance (evm : EVM.State) (principal amount : UInt256) :
    Decidable (SupplyBaseBalanceFits evm principal amount) := by
  unfold SupplyBaseBalanceFits; infer_instance

instance (evm : EVM.State) (principal amount : UInt256) :
    Decidable (SupplyBaseMathFits evm principal amount) := by
  unfold SupplyBaseMathFits; infer_instance

theorem supplyBaseBalance_int {evm : EVM.State} {principal amount : UInt256}
    (hf : SupplyBaseBalanceFits evm principal amount) :
    signedWord (supplyBaseBalance evm principal amount) =
      supplyBaseBalanceInt evm principal amount := by
  have hp := signedPresentValueWord_int evm principal hf.1
  have hb := signedWord_bounds (signedPresentValueWord evm principal)
  unfold supplyBaseBalance supplyBaseBalanceInt
  rw [signedWord_add_signed_of_range, hp, signedWord_low hf.2.1]
  · rw [hp, signedWord_low hf.2.1]
    rw [hp] at hb
    simp only [Int.ofNat_eq_natCast]
    omega
  · rw [hp, signedWord_low hf.2.1]
    exact hf.2.2

def supplyBaseMathBlock : List Stmt :=
  [.internalCall "presentValue" [.var "dstPrincipal"] "__c2",
    .internalCall "signed256" [.var "amount"] "__c3",
    .letDecl "dstBalance" (some (.elem (.int (.sint ⟨256, by decide⟩))))
      (.inRange (.sint ⟨256, by decide⟩)
      (.binary .add (.var "__c2") (.var "__c3"))),
    .internalCall "principalValue" [.var "dstBalance"] "dstPrincipalNew",
    .internalCall "repayAndSupplyAmount" [.var "dstPrincipal", .var "dstPrincipalNew"] "__c5",
    .letDecl "repayAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c5") 0),
    .letDecl "supplyAmount" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.tupleGet (.var "__c5") 1)]

def supplyBaseMathStack (evm : EVM.State) (principal ptr sender amount dst ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [supplyAmount principal (supplyBasePrincipal evm principal amount),
    repayAmount principal (supplyBasePrincipal evm principal amount),
    UInt256.ofNat 12598, ptr, supplyBasePrincipal evm principal amount,
    UInt256.ofNat 12604, amount, sender, UInt256.ofNat 12591, dst, ret] ++ R

def supplyBaseMathFrame (frame : Frame) (evm : EVM.State) (principal amount : UInt256) : Frame :=
  let next := supplyBasePrincipal evm principal amount
  let supplied := repayAmount principal next
  let borrowed := supplyAmount principal next
  { frame with
    locals := ((((((frame.locals.insert "__c2" (.int (signedPresentValueInt evm principal))).insert
      "__c3" (.int amount.toNat)).insert "dstBalance"
      (.int (supplyBaseBalanceInt evm principal amount))).insert "dstPrincipalNew"
      (.int (principalValueInt evm (supplyBaseBalance evm principal amount)))).insert "__c5"
      (.tuple [.int supplied.toNat, .int borrowed.toNat])).insert "repayAmount"
      (.int supplied.toNat)).insert "supplyAmount" (.int borrowed.toNat) }

end Benchmarks.CompoundIII.Comet
