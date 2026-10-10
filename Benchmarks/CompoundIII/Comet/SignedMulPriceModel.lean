import Benchmarks.CompoundIII.Comet.SignedDebtWords
import Benchmarks.CompoundIII.Comet.Signed256

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def signedDebtPriceValid (m p scale : UInt256) : Prop :=
  m.toNat * p.toNat ≤ 2^255 ∧ scale ≠ UInt256.ofNat 0

instance (m p scale : UInt256) : Decidable (signedDebtPriceValid m p scale) :=
  inferInstanceAs (Decidable (_ ∧ _))

def signedDebtPriceInt (m p scale : UInt256) : Int :=
  -Int.ofNat (m.toNat * p.toNat / scale.toNat)

def signedDebtPriceWord (m p scale : UInt256) : UInt256 :=
  UInt256.sub (UInt256.ofNat 0) (UInt256.div (UInt256.mul m p) scale)

theorem signedDebtPriceWord_int {m p scale : UInt256} (hp : m.toNat * p.toNat ≤ 2^255) :
    signedWord (signedDebtPriceWord m p scale) = signedDebtPriceInt m p scale := by
  have hm : (UInt256.mul m p).toNat = m.toNat * p.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt (lt_of_le_of_lt hp (by decide))]
  have hq : (UInt256.div (UInt256.mul m p) scale).toNat ≤ 2^255 := by
    rw [udiv_toNat, hm]
    exact le_trans (Nat.div_le_self _ _) hp
  rw [signedDebtPriceWord, signedWord_zeroSub_le hq, udiv_toNat, hm]
  rfl

def signedMulPriceReturnExpr : Expr :=
  .binary .sdiv (.inRange (.sint ⟨256, by decide⟩) (.binary .mul (.var "n") (.var "__c0")))
    (.cast (.cast (.var "fromScale") (.elem (.int (.uint ⟨256, by decide⟩))))
      (.elem (.int (.sint ⟨256, by decide⟩))))

def signedMulPriceCallable : CallableDecl :=
  { params := [⟨"n", .elem (.int (.sint ⟨256, by decide⟩))⟩, ⟨"price", abiUInt256⟩,
      ⟨"fromScale", .elem (.int (.uint ⟨64, by decide⟩))⟩]
    returnType := [.elem (.int (.sint ⟨256, by decide⟩))]
    body := [.internalCall "signed256" [.var "price"] "__c0", .return [signedMulPriceReturnExpr]] }

theorem signedMulPriceCallable_lookup : lookupCallable? contract "signedMulPrice" =
    some signedMulPriceCallable := rfl

def signedMulPriceEntry (imms : Store) (m p scale : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "fromScale" (.int scale.toNat)).insert "price" (.int p.toNat)
      |>.insert "n" (.int (-Int.ofNat m.toNat)) }

def signedMulPriceFinal (imms : Store) (m p scale : UInt256) : Frame :=
  let frame := signedMulPriceEntry imms m p scale
  { frame with locals := frame.locals.insert "__c0" (.int p.toNat) }

end Benchmarks.CompoundIII.Comet
