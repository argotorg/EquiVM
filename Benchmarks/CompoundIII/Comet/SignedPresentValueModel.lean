import Benchmarks.CompoundIII.Comet.PresentValue
import Benchmarks.CompoundIII.Comet.NegativePrincipal
import Benchmarks.CompoundIII.Comet.SignedWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def signedPresentMagnitude (evm : EVM.State) (principal : UInt256) (borrow : Bool) : UInt256 :=
  presentValueWord
    (totalsIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) borrow)
    (if borrow then negativePrincipal principal else positivePrincipal principal)

def signedPresentValueInt (evm : EVM.State) (principal : UInt256) : Int :=
  if 0 ≤ signed104 principal then Int.ofNat (signedPresentMagnitude evm principal false).toNat
  else -Int.ofNat (signedPresentMagnitude evm principal true).toNat

def signedPresentValueWord (evm : EVM.State) (principal : UInt256) : UInt256 :=
  if 0 ≤ signed104 principal then signedPresentMagnitude evm principal false
  else UInt256.sub (UInt256.ofNat 0) (signedPresentMagnitude evm principal true)

theorem signedPresentMagnitude_lt (evm : EVM.State) (principal : UInt256) (borrow : Bool)
    (hmin : -(2^103 : Int) < signed104 principal) :
    (signedPresentMagnitude evm principal borrow).toNat < 2^168 := by
  apply presentValueWord_lt (totalsIndexWord_lt _ borrow)
  cases borrow
  · exact lt_trans (positivePrincipal_lt _) (by decide)
  · exact lt_trans (negativePrincipal_lt hmin) (by decide)

theorem signedPresentValueWord_int (evm : EVM.State) (principal : UInt256)
    (hmin : -(2^103 : Int) < signed104 principal) :
    signedWord (signedPresentValueWord evm principal) = signedPresentValueInt evm principal := by
  unfold signedPresentValueWord signedPresentValueInt
  split_ifs
  · exact signedWord_low (lt_trans (signedPresentMagnitude_lt evm principal false hmin) (by decide))
  · rw [signedWord_sub_low (by decide)
      (lt_trans (signedPresentMagnitude_lt evm principal true hmin) (by decide))]
    simp

def signedPresentPrincipalExpr (borrow : Bool) : Expr :=
  .cast (if borrow then
      .inRange (.sint ⟨104, by decide⟩) (.binary .sub (.intLit 0) (.var "principalValue_"))
    else .var "principalValue_") (.elem (.int (.uint ⟨104, by decide⟩)))

def signedPresentReturnExpr (borrow : Bool) : Expr :=
  if borrow then .inRange (.sint ⟨256, by decide⟩) (.binary .sub (.intLit 0) (.var "__c3"))
  else .var "__c1"

def signedPresentBranch (borrow : Bool) : List Stmt :=
  [.internalCall (presentValueName borrow)
      [.storage ⟨totalsIndexName borrow, []⟩, signedPresentPrincipalExpr borrow]
      (if borrow then "__c2" else "__c0"),
    .internalCall "signed256" [.var (if borrow then "__c2" else "__c0")]
      (if borrow then "__c3" else "__c1"),
    .return [signedPresentReturnExpr borrow]]

def signedPresentCallable : CallableDecl :=
  { params := [⟨"principalValue_", .elem (.int (.sint ⟨104, by decide⟩))⟩]
    returnType := [.elem (.int (.sint ⟨256, by decide⟩))]
    body := [.ite (.binary .ge (.var "principalValue_") (.intLit 0))
      (signedPresentBranch false) (signedPresentBranch true)] }

theorem signedPresentCallable_lookup :
    lookupCallable? contract "presentValue" = some signedPresentCallable := rfl

def signedPresentEntry (imms : Store) (principal : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store).insert "principalValue_" (.int (signed104 principal)) }

end Benchmarks.CompoundIII.Comet
