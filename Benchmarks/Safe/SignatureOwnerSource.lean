import Benchmarks.Safe.SignaturePiece
import Benchmarks.Safe.OwnerStorage
import Benchmarks.Safe.Membership

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureOwnerValid (σ : AccountMap) (I : ExecutionEnv) (current last : UInt256) : Prop :=
  (UInt256.land solcAddrMask last).toNat < (UInt256.land solcAddrMask current).toNat ∧
    ownerLinkAt σ I (UInt256.land solcAddrMask current) ≠ ⟨0⟩ ∧
    UInt256.land solcAddrMask current ≠ ⟨1⟩

instance (σ : AccountMap) (I : ExecutionEnv) (current last : UInt256) :
    Decidable (signatureOwnerValid σ I current last) := inferInstanceAs (Decidable
      ((UInt256.land solcAddrMask last).toNat < (UInt256.land solcAddrMask current).toNat ∧
        ownerLinkAt σ I (UInt256.land solcAddrMask current) ≠ ⟨0⟩ ∧
        UInt256.land solcAddrMask current ≠ ⟨1⟩))

def signatureOwnerCondition : Expr :=
  andE (gtE (.var "currentOwner") (.var "lastOwner"))
    (andE (neE (.storage (ownersRef (.var "currentOwner"))) zeroAddr)
      (neE (.var "currentOwner") sentinelAddr))

theorem evalSignatureOwnerCondition {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {current last : UInt256} (hc : SignatureCore p f)
    (hcurrent : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 current)))
    (hlast : f.locals["lastOwner"]? = some (.address (AccountAddress.ofUInt256 last))) :
    evalExpr? config f evm signatureOwnerCondition =
      .ok (.bool (decide (signatureOwnerValid evm.accountMap evm.executionEnv current last))) := by
  have hf : f = { contract := contract, locals := f.locals } := by
    cases f
    simp only [Frame.mk.injEq]
    exact ⟨hc.contract, True.intro, hc.immutables⟩
  have hcur : evalExpr? config f evm (.var "currentOwner") =
      .ok (.address (AccountAddress.ofNat current.toNat)) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      (evalLocalValue (cfg := config) (evm := evm) hcurrent)
  have hlast' : evalExpr? config f evm (.var "lastOwner") =
      .ok (.address (AccountAddress.ofNat last.toNat)) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      (evalLocalValue (cfg := config) (evm := evm) hlast)
  have hgt : evalExpr? config f evm (gtE (.var "currentOwner") (.var "lastOwner")) =
      .ok (.bool (decide ((UInt256.land solcAddrMask last).toNat <
        (UInt256.land solcAddrMask current).toNat))) := by
    rw [gtE, evalExpr_binary_nonshort (by decide) (by decide), hcur, hlast']
    simp only [EvalResult.bind, bind, evalBinaryOp?, pure]
    rw [accountAddress_ofNat_toNat_eq_mask, accountAddress_ofNat_toNat_eq_mask]
  have hcur' : evalExpr? config f evm (.var "currentOwner") =
      .ok (.address (AccountAddress.ofNat (UInt256.land solcAddrMask current).toNat)) := by
    rw [hcur, addressOfNat_eq_of_masked_word current, u256_land_comm current solcAddrMask]
  have hcanonical : (UInt256.land solcAddrMask current).toNat < EVM.addressModulus := by
    rw [u256_land_comm]; exact solcAddrMask_result_canonical current
  have hload := safeEvalOwnerLink evm f.locals (.var "currentOwner")
    (UInt256.land solcAddrMask current) hc.owners hcanonical (by rw [← hf]; exact hcur')
  have hmem := evalAddressMembership hcanonical (solcAddrMask_result_canonical _)
    hcur' (by simpa only [← hf] using hload)
  have he := evalBoolAnd hgt hmem
  simpa only [signatureOwnerCondition, signatureOwnerValid, addressMembership,
    ownerLink_eq_at, Bool.decide_and] using he

def signatureNextFrame (f : Frame) (current : UInt256) (i : Nat) : Frame :=
  signatureSet (signatureSet f "lastOwner" (.address (AccountAddress.ofUInt256 current)))
    "i" (.int (Int.ofNat (i + 1)))

theorem signatureOwnerSourceAccepted {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {current last : UInt256} {i : Nat} (hc : SignatureCore p f)
    (hcurrent : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 current)))
    (hlast : f.locals["lastOwner"]? = some (.address (AccountAddress.ofUInt256 last)))
    (hi : f.locals["i"]? = some (.int (Int.ofNat i))) (hfit : i + 1 < UInt256.size)
    (hv : signatureOwnerValid evm.accountMap evm.executionEnv current last) :
    ExecBlock config f evm (signatureLoopBody.drop 5)
      (.ok (signatureNextFrame f current i) evm) := by
  have hi' : (signatureSet f "lastOwner" (.address (AccountAddress.ofUInt256 current))).locals["i"]?
      = some (.int (Int.ofNat i)) := by simp [signatureSet, Std.HashMap.getElem?_insert, hi]
  exact .consNormal (.requireTrue (by
      simpa only [hv, decide_true] using
        evalSignatureOwnerCondition (evm := evm) hc hcurrent hlast))
    (.consNormal (.assign (evalLocalValue (evm := evm) hcurrent) (by
      simp [assignStorageRef?, signatureSet, varRef, hlast, updateLocalPath?,
        EvalResult.bind, bind, pure]))
      (.consNormal (.assign (evalNatIncrement (evm := evm) (evalLocalValue hi') hfit) (by
        simp [assignStorageRef?, signatureNextFrame, signatureSet, varRef, hi, updateLocalPath?,
          EvalResult.bind, bind, pure, Std.HashMap.getElem?_insert])) .nil))

theorem signatureOwnerSourceRejected {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {current last : UInt256} (hc : SignatureCore p f)
    (hcurrent : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 current)))
    (hlast : f.locals["lastOwner"]? = some (.address (AccountAddress.ofUInt256 last)))
    (hv : ¬signatureOwnerValid evm.accountMap evm.executionEnv current last) :
    ExecBlock config f evm (signatureLoopBody.drop 5) .reverted :=
  .consRevert (.requireFalse (by
    simpa only [hv, decide_false] using
      evalSignatureOwnerCondition (evm := evm) hc hcurrent hlast))

end Benchmarks.Safe
