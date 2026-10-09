import Benchmarks.Morpho.MorphoBlue.ConstructorABI
import Benchmarks.Morpho.MorphoBlue.MarketParamsCommon
import Benchmarks.Morpho.MorphoBlue.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: round trip from a canonical address through an EVM word.
theorem address_word_roundtrip (a : AccountAddress) :
    AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
  rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt (by decide))]
  apply Fin.ext
  simp only [AccountAddress.ofNat, Fin.ofNat]
  exact Nat.mod_eq_of_lt a.isLt

def morphoDomainTypeHash : UInt256 := UInt256.ofNat
  32523383700587834770323112271211932718128200013265661849047136999858837557784

def morphoDomainWords (I : ExecutionEnv) : List UInt256 :=
  [morphoDomainTypeHash, UInt256.ofNat Ethereum.chainId, UInt256.ofNat I.codeOwner.val]

def morphoDomainSeparator (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (KEC (returnWordBytes (morphoDomainWords I)))

def morphoDomainExpr : Expr := .keccak256 (.abiEncodePacked [
  (.elem (.bytes ⟨31, by decide⟩), .keccak256 (.bytesLit "EIP712Domain(uint256 chainId,address verifyingContract)".toUTF8)),
  (abiUInt256, .env .chainid), (abiUInt256, .cast (.env .this) (.elem (.int (.uint ⟨256, by decide⟩))))])

theorem morphoDomainExpr_eval (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm morphoDomainExpr =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (morphoDomainSeparator evm.executionEnv))) := by
  have hhash : (KEC "EIP712Domain(uint256 chainId,address verifyingContract)".toUTF8).toList =
      EVM.Word.toBytesBE morphoDomainTypeHash := by native_decide
  have h0 : evalExpr? config frame evm
      (.keccak256 (.bytesLit "EIP712Domain(uint256 chainId,address verifyingContract)".toUTF8)) =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE morphoDomainTypeHash)) := by
    simp only [evalExpr?, pure, bind, EvalResult.bind, hhash]
  have h1 : evalExpr? config frame evm (.env .chainid) =
      .ok (.int (Int.ofNat (UInt256.ofNat Ethereum.chainId).toNat)) := by simp only [evalExpr?, envValue]; rfl
  have hc : (UInt256.ofNat evm.executionEnv.codeOwner.val).toNat < EVM.addressModulus := by
    have ha := evm.executionEnv.codeOwner.isLt
    rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; change _ < 2 ^ 160 at ha; omega)]
    exact ha
  have h2 : evalExpr? config frame evm (.env .this) =
      .ok (.address (AccountAddress.ofNat (UInt256.ofNat evm.executionEnv.codeOwner.val).toNat)) := by
    simp only [evalExpr?, envValue, address_word_roundtrip, pure]
  have henc0 : encodePackedValue? (.elem (.bytes ⟨31, by decide⟩))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE morphoDomainTypeHash)) =
      some (EVM.Word.toBytesBE morphoDomainTypeHash) := by
    simp [encodePackedValue?, fixedBytesSize, word_toBytesBE_length_32]
  have hpacked := evalPackedArgs_cons h0 henc0
    (evalPackedArgs_cons h1 (encodePacked_uint256 _) (evalPackedArgs_single (evalCastCanonicalAddress h2 hc)
      (encodePacked_uint256 _)))
  have hbytes : ByteArray.mk ((EVM.Word.toBytesBE morphoDomainTypeHash) ++
      (EVM.Word.toBytesBE (UInt256.ofNat Ethereum.chainId)) ++
      (EVM.Word.toBytesBE (UInt256.ofNat evm.executionEnv.codeOwner.val))).toArray =
      returnWordBytes (morphoDomainWords evm.executionEnv) := by
    apply byteArray_eq_of_toList_eq
    rw [byteArray_toList_eq, List.toList_toArray, returnWordBytes_toList]
    simp only [morphoDomainWords, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  simp only [morphoDomainExpr, evalExpr?, hpacked, pure, bind, EvalResult.bind]
  rw [← List.append_assoc, hbytes, morphoDomainSeparator, toBytesBE_keccak_uInt256OfByteArray]

def morphoConstructorArgs (a : AccountAddress) : Store := (∅ : Store).insert "newOwner" (.address a)
def morphoConstructorFrame (a : AccountAddress) : Frame :=
  { contract := contract, locals := morphoConstructorArgs a, immutables := initialImmutables contract }
def morphoConstructorFinal (a : AccountAddress) (I : ExecutionEnv) : Frame :=
  { morphoConstructorFrame a with immutables := ((initialImmutables contract).insert "DOMAIN_SEPARATOR"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (morphoDomainSeparator I)))) }

def morphoConstructorState (evm : EVM.State) (a : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) (UInt256.ofNat a.val))

theorem morphoConstructorOwner_eval (a : AccountAddress) (evm : EVM.State) :
    evalExpr? config (morphoConstructorFrame a) evm
      (.binary .ne (.var "newOwner") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (a ≠ AccountAddress.ofNat 0))) := by
  simp only [evalExpr?, morphoConstructorFrame, morphoConstructorArgs, store_get_self,
    EvalResult.ofOption, evalBinaryOp?, castValue?, bind, EvalResult.bind, pure,
    show ¬ (0 : Int) < 0 from by decide, ↓reduceIte, Int.toNat_zero]
  simp only [show (Value.address a == Value.address (AccountAddress.ofNat 0)) = decide (a = AccountAddress.ofNat 0) by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq], decide_not]

theorem morphoConstructorSource (a : AccountAddress) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩) (hne : a ≠ AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (morphoConstructorArgs a) contract.ctor.body
      (.returned (morphoConstructorFinal a evm.executionEnv) (morphoConstructorState evm a) none)
      (initialImmutables contract) := by
  apply ExecFuncBody.execBlockOK
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv))
  apply ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [decide_eq_true hne] using morphoConstructorOwner_eval a evm))
  apply ExecBlock.consNormal (ExecStmt.setImmutable (morphoDomainExpr_eval _ _) rfl (by
    simp [elemValueFits, word_toBytesBE_length_32]))
  have hc : (UInt256.ofNat a.val).toNat < EVM.addressModulus := by
    have ha := a.isLt
    rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; change _ < 2 ^ 160 at ha; omega)]
    exact ha
  have hv : AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    exact address_word_roundtrip a
  apply ExecBlock.consNormal (ExecStmt.assign (value := .address a) ?_ ?_)
  · apply ExecBlock.consNormal (ExecStmt.emit (vals := [.address a]) ?_)
    · exact ExecBlock.nil
    · simp only [evalExprs?, evalExpr?, morphoConstructorFinal, morphoConstructorFrame,
        morphoConstructorArgs, store_get_self, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · simp only [evalExpr?, morphoConstructorFinal, morphoConstructorFrame,
      morphoConstructorArgs, store_get_self, EvalResult.ofOption]
  · simpa only [hv] using assignMorphoAddress evm (morphoConstructorArgs a)
      (morphoConstructorFinal a evm.executionEnv).immutables "owner" ⟨0⟩ (UInt256.ofNat a.val)
      (by simp [morphoConstructorArgs]) rfl rfl hc


theorem morphoConstructorSourceRejects (a : AccountAddress) (evm : EVM.State)
    (hbad : evm.executionEnv.weiValue ≠ ⟨0⟩ ∨ a = AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (morphoConstructorArgs a) contract.ctor.body .reverted
      (initialImmutables contract) := by
  rcases hbad with hcv | ha
  · exact bodyReverts_nonPayable hcv
  · by_cases hcv : evm.executionEnv.weiValue = ⟨0⟩
    · apply ExecFuncBody.execBlockRevert
      apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv))
      apply ExecBlock.consRevert
      apply ExecStmt.requireFalse
      simpa only [ha, ne_eq, not_true_eq_false, decide_false] using morphoConstructorOwner_eval a evm
    · exact bodyReverts_nonPayable hcv

theorem morphoConstructorExec {σ σ₀ A I} {g : UInt256} {res : ExecResult} (a : AccountAddress)
    (hb : ExecTransitionBody config contract (initState σ σ₀ (.ofUInt256 g) A I)
      (morphoConstructorArgs a) contract.ctor.body res (initialImmutables contract)) :
    solmCtorExec config contract [.address a] σ σ₀ g A I res := by
  exact solmCtorExec.intro rfl rfl rfl hb

theorem morphoConstructorFinal_fit (a : AccountAddress) (I : ExecutionEnv) :
    immutablesFit contract (morphoConstructorFinal a I).immutables := by
  intro d hd
  have hd' : d = ⟨"DOMAIN_SEPARATOR", .bytes ⟨31, by decide⟩⟩ := by
    simpa only [contract, Syntax.contractSyntax, List.mem_cons, List.not_mem_nil, or_false] using hd
  subst d
  refine ⟨_, store_get_self _ _ _, ?_⟩
  simp [elemValueFits, word_toBytesBE_length_32]

theorem morphoConstructorFinal_word (a : AccountAddress) (I : ExecutionEnv) :
    wordsOf (morphoConstructorFinal a I).immutables "DOMAIN_SEPARATOR" = morphoDomainSeparator I :=
  wordsOf_of_get (store_get_self _ _ _) (valueToWord_bytes32_word _)

end Benchmarks.Morpho.MorphoBlue
