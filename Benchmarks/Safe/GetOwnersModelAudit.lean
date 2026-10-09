import Benchmarks.Safe.GetOwnersSource
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

/-!
Regression coverage for the former memory-reader cutoff in getOwners. The updated
reader preserves the entire large ABI result. These symbolic lemmas do not allocate
an enormous array in the evaluator and do not assert a full bytecode execution.
-/

def hugeOwnerCount : Nat := 2 ^ 59 - 2

theorem hugeOwnerCount_allowed : hugeOwnerCount ≤ 2 ^ 64 - 1 := by
  norm_num [hugeOwnerCount]

theorem hugeOwnerReturnLength : 64 + 32 * hugeOwnerCount = 2 ^ 64 := by
  norm_num [hugeOwnerCount]

def zeroOwnerReturnBytes (n : Nat) : ByteArray :=
  (natBytes 32 ++ (natBytes n ++
    (List.replicate n (⟨0⟩ : UInt256)).flatMap EVM.Word.toBytesBE)).toByteArray

theorem zeroOwnerStaticEncoding (n : Nat) :
    encodeABIStaticArrayElems? addr
      ((List.replicate n (⟨0⟩ : UInt256)).map addressArrayValue) =
      some ((List.replicate n (⟨0⟩ : UInt256)).flatMap EVM.Word.toBytesBE) := by
  have hz : encodeABIValue? addr (addressArrayValue ⟨0⟩) =
      some (EVM.Word.toBytesBE ⟨0⟩) := by
    simpa only [solcAddrMask_clean (by decide : (⟨0⟩ : UInt256).toNat < EVM.addressModulus),
      ← word_toBytesBE_eq_toByteArray_toList] using encodeABIValue_address_word ⟨0⟩
  induction n with
  | zero => simp [encodeABIStaticArrayElems?]
  | succ n ih =>
      simp only [List.replicate_succ, List.map_cons, List.flatMap_cons,
        encodeABIStaticArrayElems?, hz, ih, bind, Option.bind, pure]

theorem zeroOwnerReturnEncoding (n : Nat) :
    encodeReturnValues? [.dynamicArray addr]
      [.array ((List.replicate n (⟨0⟩ : UInt256)).map addressArrayValue)] =
      some (zeroOwnerReturnBytes n) := by
  unfold encodeReturnValues?
  rw [encodeABIValues_single_dynArray_static (by rfl), zeroOwnerStaticEncoding]
  simp only [List.length_map, List.length_replicate, bind, Option.bind, pure]
  simp only [byteArray_mk_toArray_eq_toByteArray, zeroOwnerReturnBytes]

theorem zeroOwnerReturnSize (n : Nat) : (zeroOwnerReturnBytes n).size = 64 + 32 * n := by
  have hs : ((List.replicate n (⟨0⟩ : UInt256)).flatMap EVM.Word.toBytesBE).length = 32 * n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ, List.flatMap_cons, List.length_append,
          word_toBytesBE_length_32, ih]
        omega
  simp only [zeroOwnerReturnBytes, List.size_toByteArray, List.length_append, hs,
    natBytes, word_toBytesBE_length_32]
  omega

theorem hugeOwnerReturnNonempty : zeroOwnerReturnBytes hugeOwnerCount ≠ ByteArray.empty := by
  intro h
  have hs := congrArg ByteArray.size h
  rw [zeroOwnerReturnSize, hugeOwnerReturnLength] at hs
  norm_num at hs

theorem safeGetOwnersEarlyReturn (evm : EVM.State)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : (ownerCount evm).toNat ≤ 2 ^ 64 - 1)
    (hcurrent : ownerLink evm ⟨1⟩ = ⟨1⟩) :
    ExecTransitionBody config contract evm ∅ getownersTransition.body
      (.returned { contract := contract, locals := getOwnersInitialLocals evm } evm
        (some [.array ((List.replicate (ownerCount evm).toNat ⟨0⟩).map addressArrayValue)])) := by
  have hl := safeGetOwnersInitialLocals evm
  have hc := safeGetOwnersCondition evm hl (solcAddrMask_result_canonical _)
  exact ExecFuncBody.execBlockRet (safeGetOwnersPrefix evm hvalue hlen
    (.consNormal (.whileFalse (by simpa only [hcurrent, ne_eq, not_true_eq_false,
      decide_false] using hc)) (safeGetOwnersReturn evm hl)))

-- Arithmetic check only: the complete bytecode gas cost still needs a trace proof.
theorem hugeOwnerMemoryCostFits :
    Cₘ (UInt256.ofNat (2 ^ 60 + 16)) + 1000 * hugeOwnerCount + 1000000 < 2 ^ 200 := by
  decide +kernel

def hugeOwnerAuditAccount : Account :=
  { (default : Account) with
    storage := ((∅ : Storage).insert ⟨3⟩ (UInt256.ofNat hugeOwnerCount)).insert
      (mapSlot ⟨1⟩ ⟨2⟩) ⟨1⟩ }

def hugeOwnerAuditState (perm : Bool) : EVM.State :=
  { (default : EVM.State) with
    accountMap := (∅ : AccountMap).insert (AccountAddress.ofNat 4096) hugeOwnerAuditAccount
    executionEnv := { (default : ExecutionEnv) with
      codeOwner := AccountAddress.ofNat 4096, code := safeBytecode,
      calldata := ⟨#[0xa0, 0xe6, 0x7e, 0x2b]⟩, weiValue := ⟨0⟩, perm := perm }
    machineState.gasAvailable := Sat256.ofUInt256 (UInt256.ofNat (2 ^ 200)) }

theorem hugeOwnerAudit_count (perm : Bool) :
    (ownerCount (hugeOwnerAuditState perm)).toNat = hugeOwnerCount := by
  have hslot : mapSlot ⟨1⟩ ⟨2⟩ ≠ (⟨3⟩ : UInt256) := by native_decide
  simp [ownerCount, hugeOwnerAuditState, hugeOwnerAuditAccount, Solm.EVM.storageLoad,
    State.lookupAccount, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getD, hslot, Ne.symm hslot]
  decide +kernel

theorem hugeOwnerAudit_current (perm : Bool) :
    ownerLink (hugeOwnerAuditState perm) ⟨1⟩ = ⟨1⟩ := by
  simp [ownerLink, hugeOwnerAuditState, hugeOwnerAuditAccount, Solm.EVM.storageLoad,
    State.lookupAccount, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getD_insert_self, Option.option, Account.lookupStorage,
    solcAddrMask_clean (by decide : (⟨1⟩ : UInt256).toNat < EVM.addressModulus)]

theorem hugeOwnerAudit_source (perm : Bool) :
    ExecTransitionBody config contract (hugeOwnerAuditState perm) ∅ getownersTransition.body
      (.returned { contract := contract, locals := getOwnersInitialLocals (hugeOwnerAuditState
        perm) }
        (hugeOwnerAuditState perm)
        (some [.array ((List.replicate hugeOwnerCount ⟨0⟩).map addressArrayValue)])) := by
  simpa only [hugeOwnerAudit_count] using safeGetOwnersEarlyReturn
    (hugeOwnerAuditState perm) rfl (by rw [hugeOwnerAudit_count]; exact hugeOwnerCount_allowed)
    (hugeOwnerAudit_current perm)

theorem hugeOwnerAudit_noEmptyABI :
    ¬ returnEquiv ByteArray.empty
      (some [.array ((List.replicate hugeOwnerCount ⟨0⟩).map addressArrayValue)])
      [.dynamicArray addr] := by
  intro h
  cases h with
  | returned hv he =>
      cases hv
      rw [zeroOwnerReturnEncoding] at he
      exact hugeOwnerReturnNonempty (Option.some.inj he)
  | fallthrough hv _ _ => cases hv

theorem hugeOwner_readsExpectedABI :
    (zeroOwnerReturnBytes hugeOwnerCount).readWithPadding 0
      (64 + 32 * hugeOwnerCount) = zeroOwnerReturnBytes hugeOwnerCount := by
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega)
    (by rw [zeroOwnerReturnSize]; omega)]
  simpa only [Nat.zero_add, ← zeroOwnerReturnSize] using
    byteArray_extract_self (zeroOwnerReturnBytes hugeOwnerCount)

end Benchmarks.Safe
