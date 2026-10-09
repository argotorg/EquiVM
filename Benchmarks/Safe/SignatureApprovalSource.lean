import Benchmarks.Safe.SignatureBranchSource
import Benchmarks.Safe.OwnerStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureApprovalWord (σ : AccountMap) (I : ExecutionEnv) (owner hash : UInt256) : UInt256 :=
  solcSlotWordAt (mapSlot hash (mapSlot (UInt256.land solcAddrMask owner) ⟨8⟩)) σ I

def signatureApproved (σ : AccountMap) (I : ExecutionEnv)
    (executor owner hash : UInt256) : Prop :=
  UInt256.land solcAddrMask executor = UInt256.land solcAddrMask owner ∨
    signatureApprovalWord σ I owner hash ≠ ⟨0⟩

instance (σ : AccountMap) (I : ExecutionEnv) (executor owner hash : UInt256) :
    Decidable (signatureApproved σ I executor owner hash) := inferInstanceAs (Decidable
      (UInt256.land solcAddrMask executor = UInt256.land solcAddrMask owner ∨
        signatureApprovalWord σ I owner hash ≠ ⟨0⟩))

def signatureApprovalCondition : Expr :=
  orE (eqE (.var "executor") (.var "currentOwner"))
    (neE (.storage (approvedHashesRef (.var "currentOwner") (.var "dataHash"))) (.intLit 0))

def signatureApprovalBody : List Stmt :=
  [ .assign .localVar (varRef "currentOwner")
      (uint256AsAddress (bytes32AsUint256 (.var "r"))),
    .require signatureApprovalCondition ]

theorem evalSignatureApprovalWord {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {owner : UInt256} (hc : SignatureCore p f)
    (ho : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner))) :
    evalExpr? config f evm
      (.storage (approvedHashesRef (.var "currentOwner") (.var "dataHash"))) =
      .ok (uint256Value (signatureApprovalWord evm.accountMap evm.executionEnv owner p.hash)) := by
  have ho' : evalExpr? config f evm (.var "currentOwner") =
      .ok (.address (AccountAddress.ofNat (UInt256.land solcAddrMask owner).toNat)) := by
    rw [evalLocalValue ho, accountAddress_ofUInt256_eq_ofNat_toNat,
      addressOfNat_eq_of_masked_word owner, u256_land_comm owner solcAddrMask]
  apply evalExpr_storage_scalar_value (er := { base := "approvedHashes", steps :=
      [.mindex (.address (AccountAddress.ofNat (UInt256.land solcAddrMask owner).toNat)),
        .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE p.hash))] })
    (loc := uint256Loc (mapSlot p.hash (mapSlot (UInt256.land solcAddrMask owner) ⟨8⟩)))
  · exact hc.approvedHashes
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, approvedHashesRef,
      ho', evalLocalValue hc.hash, valueToKey?, wordBytes32Value, abiBytes32Width,
      word_toBytesBE_length_32, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rw [hc.contract]; rfl
  · rfl
  · change some (StorageAddr.leaf (wordLoc (mapSlot (keyValueToWord
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE p.hash))) (mapSlot
        (keyValueToWord (.address
          (AccountAddress.ofNat (UInt256.land solcAddrMask owner).toNat))) ⟨8⟩))
        (.int uint256Int))) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE p.hash)) = p.hash
      from keyValueToWord_fixedBytes32 p.hash, keyValueToWord_address_of_canonical _ (by
      rw [u256_land_comm]; exact solcAddrMask_result_canonical owner)]
    rfl
  · simpa only [signatureApprovalWord, uint256Value, storageLoad_eq_solcSlotWord] using
      storageLocLoad_uint256 evm (mapSlot p.hash (mapSlot (UInt256.land solcAddrMask owner) ⟨8⟩))

theorem evalSignatureApprovalCondition {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {owner executor : UInt256} (hc : SignatureCore p f)
    (he : p.executor = AccountAddress.ofUInt256 executor)
    (ho : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner))) :
    evalExpr? config f evm signatureApprovalCondition = .ok (.bool
      (decide (signatureApproved evm.accountMap evm.executionEnv executor owner p.hash))) := by
  have hm (w : UInt256) : (UInt256.land solcAddrMask w).toNat < EVM.addressModulus := by
    rw [u256_land_comm]; exact solcAddrMask_result_canonical w
  have heval {name : Ident} {w : UInt256}
      (hl : f.locals[name]? = some (.address (AccountAddress.ofUInt256 w))) :
      evalExpr? config f evm (.var name) =
        .ok (.address (AccountAddress.ofNat (UInt256.land solcAddrMask w).toNat)) := by
    rw [evalLocalValue hl, accountAddress_ofUInt256_eq_ofNat_toNat,
      addressOfNat_eq_of_masked_word w, u256_land_comm w solcAddrMask]
  have heq := evalAddressEq (hm executor) (hm owner)
    (heval (by simpa only [he] using hc.executor)) (heval ho)
  have hne : evalExpr? config f evm
      (neE (.storage (approvedHashesRef (.var "currentOwner") (.var "dataHash"))) (.intLit 0)) =
      .ok (.bool (decide
        (signatureApprovalWord evm.accountMap evm.executionEnv owner p.hash ≠ ⟨0⟩))) := by
    rw [neE, evalExpr_binary_nonshort (by decide) (by decide), evalSignatureApprovalWord hc ho]
    simp [evalExpr?, evalBinaryOp?, uint256Value, EvalResult.bind, bind, pure]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq, Int.ofNat_eq_natCast,
      Int.natCast_eq_zero]
    exact ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩
  simpa only [signatureApprovalCondition, signatureApproved, Bool.decide_or] using
    evalBoolOr heq hne

theorem signatureApprovalSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r executor : UInt256} {old : Value} (hc : SignatureCore p f)
    (he : p.executor = AccountAddress.ofUInt256 executor)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (ho : f.locals["currentOwner"]? = some old) :
    ExecBlock config f evm signatureApprovalBody
      (if signatureApproved evm.accountMap evm.executionEnv executor r p.hash
        then .ok (signatureCurrentFrame f r) evm else .reverted) := by
  have hcond := evalSignatureApprovalCondition (evm := evm) (owner := r) (hc.current r) he
    (by simp [signatureCurrentFrame, signatureSet, Std.HashMap.getElem?_insert])
  by_cases h : signatureApproved evm.accountMap evm.executionEnv executor r p.hash
  · rw [if_pos h]
    exact .consNormal (signatureCurrentSource hr ho)
      (.consNormal (.requireTrue (by simpa only [h, decide_true] using hcond)) .nil)
  · rw [if_neg h]
    exact .consNormal (signatureCurrentSource hr ho)
      (.consRevert (.requireFalse (by simpa only [h, decide_false] using hcond)))

end Benchmarks.Safe
