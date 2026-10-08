import Benchmarks.CompoundIII.Comet.PriceDecode
import Benchmarks.CompoundIII.Comet.StaticCallBridge
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def pricePayload : ByteArray := ByteArray.mk #[254, 175, 150, 140]

def pricePayloadExpr : Expr :=
  .abiEncodePacked [(.elem (.bytes ⟨3, by decide⟩),
    .fixedBytesLit ⟨3, by decide⟩ [254, 175, 150, 140])]

def pricePrefix : List Stmt :=
  [.letDecl "payload" (some .bytes) pricePayloadExpr,
    .lowLevelCall (.var "priceFeed") (.intLit 0) (.var "payload") "ok" "result" (perm := false)]

def priceRemainder : List Stmt :=
  [.require (.var "ok"), .letDecl "__c0" none (.abiDecode priceRoundType (.var "result")),
    .letDecl "price" (some (.elem (.int (.sint ⟨256, by decide⟩)))) (.tupleGet (.var "__c0") 1),
    .require (.binary .gt (.var "price") (.intLit 0)),
    .return [.cast (.var "price") (.elem (.int (.uint ⟨256, by decide⟩)))]]

def priceCallable : CallableDecl :=
  { params := [⟨"priceFeed", .elem .address⟩]
    returnType := [abiUInt256]
    body := pricePrefix ++ priceRemainder }

theorem priceCallable_lookup :
    lookupCallable? contract "getPrice_body" = some priceCallable := rfl

def priceEntry (imms : Store) (addr : AccountAddress) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "priceFeed" (.address addr),
    immutables := imms }

def priceCallFrame (imms : Store) (addr : AccountAddress) (z : Bool) (out : ByteArray) : Frame :=
  let f := priceEntry imms addr
  { f with locals := ((f.locals.insert "payload" (.bytes pricePayload)).insert "ok"
    (.bool z)).insert "result" (.bytes out) }

def priceDecodedFrame (imms : Store) (addr : AccountAddress) (out : ByteArray) : Frame :=
  let f := priceCallFrame imms addr true out
  { f with
    locals := (f.locals.insert "__c0" (priceRoundValue out)).insert "price"
      (.int (signedPrice (calldataWord out 32))) }

def PriceValid (out : ByteArray) : Prop :=
  160 ≤ out.size ∧ PriceRoundCanonical out ∧ 0 < signedPrice (calldataWord out 32)

instance (out : ByteArray) : Decidable (PriceValid out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem signedPrice_of_pos {w : UInt256} (hp : 0 < signedPrice w) :
    signedPrice w = Int.ofNat w.toNat := by
  have hw : w.toNat < 2^256 := w.val.isLt
  unfold signedPrice at hp ⊢
  split_ifs with h
  · rfl
  · simp only [Int.ofNat_eq_natCast] at hp ⊢
    norm_num at hp
    omega

theorem pricePayload_eval (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm pricePayloadExpr = .ok (.bytes pricePayload) := by
  simp [pricePayloadExpr, pricePayload, evalExpr?, evalPackedArgs?, encodePackedValue?,
    pure, bind, EvalResult.bind]

theorem pricePrefix_exec (imms : Store) (addr : AccountAddress) (evm evm' : EVM.State)
    (z : Bool) (out : ByteArray)
    (hc : callViaEVM evm addr 0 pricePayload (z, evm', out) false) :
    ExecBlock config (priceEntry imms addr) evm pricePrefix
      (.ok (priceCallFrame imms addr z out) evm') := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (pricePayload_eval _ _))
  apply ExecBlock.consNormal (lowLevelCallSourceWithPerm (target := addr)
    (value := 0) (calldata := pricePayload) ?_ (by simp only [evalExpr?, pure]) ?_ hc)
  · exact ExecBlock.nil
  all_goals
    simp only [evalExpr?, priceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl

theorem priceDecoded_exec (imms : Store) (addr : AccountAddress) (evm : EVM.State)
    (out : ByteArray) (hlo : 160 ≤ out.size) (hhi : out.size < 2^255)
    (hcanon : PriceRoundCanonical out) :
    ExecBlock config (priceCallFrame imms addr true out) evm
      (priceRemainder.take 3) (.ok (priceDecodedFrame imms addr out) evm) := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
    · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
      simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption, pure, bind, EvalResult.bind, priceRoundValue, tupleGetValue?]
      rfl
    · have hd := priceRoundDecode_result hlo hhi
      rw [if_pos hcanon] at hd
      simp only [evalExpr?, priceCallFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
      change (match decodeReturnValueWithMode? .modern priceRoundType out with
        | some value => EvalResult.ok value | none => .revert) = _
      rw [hd]
  · simp only [evalExpr?, priceCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl

theorem priceRemainder_returns (imms : Store) (addr : AccountAddress) (evm : EVM.State)
    (out : ByteArray) (hhi : out.size < 2^255) (hv : PriceValid out) :
    ExecBlock config (priceCallFrame imms addr true out) evm priceRemainder
      (.returned (priceDecodedFrame imms addr out) evm
        (some [.int (calldataWord out 32).toNat])) := by
  have hd := priceDecoded_exec imms addr evm out hv.1 hhi hv.2.1
  change ExecBlock config _ _ (priceRemainder.take 3 ++ priceRemainder.drop 3) _
  apply execBlockAppendOk hd
  have hp : evalExpr? config (priceDecodedFrame imms addr out) evm (.var "price") =
      .ok (.int (signedPrice (calldataWord out 32))) := by
    simp only [evalExpr?, priceDecodedFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  apply ABlock.returns (ABlock.start.requireStep ?_)
  · have he := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) hp
    rw [signedPrice_of_pos hv.2.2, normalizeInt_uint256_word] at he
    exact he
  · simp only [evalExpr?, hp, pure, bind, EvalResult.bind, evalBinaryOp?,
      decide_eq_true hv.2.2]

theorem priceRemainder_reverts (imms : Store) (addr : AccountAddress) (evm : EVM.State)
    (out : ByteArray) (z : Bool) (hhi : out.size < 2^255)
    (hv : ¬ (z = true ∧ PriceValid out)) :
    ExecBlock config (priceCallFrame imms addr z out) evm priceRemainder .reverted := by
  cases z with
  | false =>
      apply ABlock.start.requireRevert
      simp only [evalExpr?, priceCallFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl
  | true =>
      by_cases hlo : 160 ≤ out.size
      · by_cases hcanon : PriceRoundCanonical out
        · have hn : ¬ 0 < signedPrice (calldataWord out 32) :=
            fun hp ↦ hv ⟨rfl, hlo, hcanon, hp⟩
          change ExecBlock config _ _ (priceRemainder.take 3 ++ priceRemainder.drop 3) _
          apply execBlockAppendOk (priceDecoded_exec imms addr evm out hlo hhi hcanon)
          apply ABlock.start.requireRevert
          simp only [evalExpr?, priceDecodedFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption, pure, bind, EvalResult.bind,
            evalBinaryOp?]
          change EvalResult.ok (Value.bool (decide (0 < signedPrice (calldataWord out 32)))) = _
          rw [decide_eq_false hn]
        · have hd := priceRoundDecode_result hlo hhi
          rw [if_neg hcanon] at hd
          apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
          · apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
            simp only [evalExpr?, priceCallFrame, Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
            change (match decodeReturnValueWithMode? .modern priceRoundType out with
              | some value => EvalResult.ok value | none => .revert) = _
            rw [hd]
          · simp only [evalExpr?, priceCallFrame, Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insert, EvalResult.ofOption]
            rfl
      · have hd := priceRoundDecode_short (Nat.lt_of_not_ge hlo)
        apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
        · apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
          simp only [evalExpr?, priceCallFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
          change (match decodeReturnValueWithMode? .modern priceRoundType out with
            | some value => EvalResult.ok value | none => .revert) = _
          rw [hd]
        · simp only [evalExpr?, priceCallFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]
          rfl

end Benchmarks.CompoundIII.Comet
