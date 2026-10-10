import Benchmarks.Morpho.MetaMorphoV1_1.PackedSource

/-! Source decoding of the immutable short strings used by EIP-712. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def shortStringLength (word : UInt256) : UInt256 := UInt256.land word ⟨255⟩

def shortStringBytes (word : UInt256) : ByteArray :=
  word.toByteArray.extract 0 (shortStringLength word).toNat

def shortStringValid (word : UInt256) : Prop := (shortStringLength word).toNat ≤ 31

instance (word : UInt256) : Decidable (shortStringValid word) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem shortStringBytes_size (word : UInt256) (h : shortStringValid word) :
    (shortStringBytes word).size = (shortStringLength word).toNat := by
  rw [shortStringBytes, ByteArray.size_extract, toByteArray_size]
  unfold shortStringValid at h
  omega

-- LIBRARY CANDIDATE: unsigned bitwise conjunction on two EVM words.
theorem evalExpr_wordAnd {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg frame evm (.binary (.bitAnd (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (uint256Value (UInt256.land a b)) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [ha, hb, uint256Value, bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise,
    IntType.bitWidth, normalizeInt_uint256_word]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  have hsmall : Nat.land a.toNat b.toNat < UInt256.size :=
    lt_of_le_of_lt (nat_land_le_right _ _) b.val.isLt
  rw [u256_land_toNat, Nat.mod_eq_of_lt hsmall]
  rw [normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hsmall)]

def shortStringFunction : FunctionDecl := contract.functions[89]!

def shortStringFrame (imms : Store) (word : UInt256) : Frame :=
  ⟨contract, (∅ : Store).insert "sstr" (wordBytes32Value word), imms⟩

def shortStringLengthFrame (imms : Store) (word : UInt256) : Frame :=
  { shortStringFrame imms word with
    locals := (shortStringFrame imms word).locals.insert "len"
      (uint256Value (shortStringLength word)) }

def shortStringResultFrame (imms : Store) (word : UInt256) : Frame :=
  { shortStringLengthFrame imms word with
    locals := (shortStringLengthFrame imms word).locals.insert "value" (.bytes word.toByteArray) }

theorem shortStringLengthSource (evm : State) (imms : Store) (word : UInt256) :
    evalExpr? config (shortStringFrame imms word) evm
      (.binary (.bitAnd (.uint ⟨256, by decide⟩))
        (.cast (.var "sstr") (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 255)) =
      .ok (uint256Value (shortStringLength word)) := by
  apply evalExpr_wordAnd
  · apply evalExpr_bytes32ToUint
    simp only [evalExpr?, shortStringFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, pure]; rfl

theorem shortStringCheckSource (evm : State) (imms : Store) (word : UInt256) :
    evalExpr? config (shortStringLengthFrame imms word) evm
      (.binary .le (.var "len") (.intLit 31)) =
      .ok (.bool (decide (shortStringValid word))) := by
  apply naturalLeSource
  · simp only [evalExpr?, shortStringLengthFrame, store_get_self, EvalResult.ofOption,
      uint256Value]
  · simp only [evalExpr?, pure]; rfl

theorem shortStringBodyReturns (evm : State) (imms : Store) (word : UInt256)
    (hvalid : shortStringValid word) :
    ExecFuncBody config (shortStringFrame imms word) evm shortStringFunction.body
      (.returned (shortStringResultFrame imms word) evm (some [.bytes (shortStringBytes word)])) :=
    by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.letDecl (shortStringLengthSource evm imms word))
  apply ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [hvalid, decide_true] using shortStringCheckSource evm imms word))
  have hs : evalExpr? config (shortStringLengthFrame imms word) evm (.var "sstr") =
      .ok (wordBytes32Value word) := by
    simp only [evalExpr?, shortStringLengthFrame, shortStringFrame,
      store_get_ne _ _ (show ("len" == "sstr") = false by decide), store_get_self,
      EvalResult.ofOption]
  have hp := evalExpr_packed (evalPackedArgs_cons hs (encodePacked_bytes32 word)
    (args := []) (tail := []) (by simp only [evalPackedArgs?, pure]))
  simp only [List.append_nil, word_toBytesBE_toByteArray_eq_toByteArray] at hp
  apply ExecBlock.consNormal (ExecStmt.letDecl hp)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, shortStringLengthFrame,
    store_get_self, store_get_ne _ _ (show ("value" == "len") = false by decide),
    EvalResult.ofOption, uint256Value, bind, EvalResult.bind, pure]
  exact sliceBytes_nat (start := 0) (Nat.zero_le _)
    (by rw [toByteArray_size]; exact Nat.le_trans hvalid (by omega))

theorem shortStringBodyReverts (evm : State) (imms : Store) (word : UInt256)
    (hbad : ¬ shortStringValid word) :
    ExecFuncBody config (shortStringFrame imms word) evm shortStringFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (ExecStmt.letDecl (shortStringLengthSource evm imms word))
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    simpa only [hbad, decide_false] using shortStringCheckSource evm imms word))

end Benchmarks.Morpho.MetaMorphoV1_1
