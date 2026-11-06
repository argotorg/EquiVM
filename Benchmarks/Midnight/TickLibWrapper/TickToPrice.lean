import Benchmarks.Midnight.TickLibWrapper.WExp

/-!
# TickLibWrapper `tickToPrice(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 359; reach lemma `tickLibWrapperReachTickToPriceBody`.

`tickToPrice_body` internally calls `wExp_body` on `LN * (3372 - tick)`; the wExp machinery
(`wExpPos`, `wExpVal`, `wExpBodyStele`, `wExp636_stack`) is reused verbatim.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight.TickLibWrapper

set_option maxRecDepth 2000000

private abbrev sint256T : IntType := .sint ⟨256, by decide⟩
private abbrev uint256T : IntType := .uint ⟨256, by decide⟩
private abbrev sint256S : StorageType := .elem (.int sint256T)
private abbrev uint256S : StorageType := .elem (.int uint256T)

private abbrev LNI : Int := 4987541511039073

/-- The `wExp_body` argument in `tickToPrice_body`: `LN * (3372 - tick)`. -/
def ttpArg (t : Nat) : Int := LNI * (3372 - Int.ofNat t)

/-- `uint256(1e18 + c0)` — the `__d1` denominator. -/
def ttpDen (c0 : Int) : Int := normalizeInt uint256T (1000000000000000000 + c0)

/-- The spec `__d1`: `uint256((1e36 + ((uint256(1e18+c0)-1)/2)) / uint256(1e18+c0))`. -/
def ttpD1 (c0 : Int) : Int :=
  normalizeInt uint256T
    (normalizeInt uint256T
      (1000000000000000000000000000000000000 + (ttpDen c0 - 1) / 2) / ttpDen c0)

/-- The spec `__d2`: `uint256((uint256(__d1 + (1e11-1)/2)) / 1e11)`. -/
def ttpD2 (c0 : Int) : Int :=
  normalizeInt uint256T (normalizeInt uint256T (ttpD1 c0 + 49999999999) / 100000000000)

/-- The full `tickToPrice_body` result `uint256(__d2 * 1e11)`. -/
def ttpResult (t : Nat) : Int :=
  normalizeInt uint256T (ttpD2 (wExpVal (ttpArg t)) * 100000000000)

/-- `|ttpArg t| ≤ LN * 3372 < 2^255` for `t ≤ 6744`. -/
theorem ttpArg_bound {t : Nat} (ht : t ≤ 6744) :
    -(2 ^ 255 : Int) < ttpArg t ∧ ttpArg t < 2 ^ 255 := by
  show -(2 ^ 255 : Int) < 4987541511039073 * (3372 - (t : Int)) ∧
    4987541511039073 * (3372 - (t : Int)) < 2 ^ 255
  omega

/-- `ttpArg t` is never the `wExp_body` minimum input for `t ≤ 6744`. -/
theorem ttpArg_ne_min {t : Nat} (ht : t ≤ 6744) :
    ttpArg t ≠
      -(57896044618658097711785492504343953926634992332820282019728792003956564819968) := by
  have h := (ttpArg_bound ht).1
  omega

theorem ttpArg_sintNorm {t : Nat} (ht : t ≤ 6744) :
    normalizeInt sint256T (ttpArg t) = ttpArg t :=
  sintNorm_of_mem _ (le_of_lt (ttpArg_bound ht).1) (ttpArg_bound ht).2

/-- `normalizeInt uint256` residues are in `[0, 2^256)`. -/
theorem uNorm_nonneg (i : Int) : 0 ≤ normalizeInt uint256T i := by
  show 0 ≤ i % Int.ofNat (EVM.twoPow 256)
  exact Int.emod_nonneg _ (by native_decide)

theorem uNorm_lt_mod (i : Int) : normalizeInt uint256T i < Int.ofNat EVM.wordModulus := by
  show i % Int.ofNat (EVM.twoPow 256) < Int.ofNat EVM.wordModulus
  rw [show Int.ofNat EVM.wordModulus = Int.ofNat (EVM.twoPow 256) from rfl]
  exact Int.emod_lt_of_pos _ (by native_decide)

theorem ttpResult_nonneg (t : Nat) : 0 ≤ ttpResult t := uNorm_nonneg _
theorem ttpResult_lt_mod (t : Nat) : ttpResult t < Int.ofNat EVM.wordModulus := uNorm_lt_mod _

theorem ttpResult_toNat (t : Nat) :
    Int.ofNat (EVM.wordOfInt (ttpResult t)).toNat = ttpResult t := by
  rw [wordOfInt_toNat, Int.emod_eq_of_lt (ttpResult_nonneg t) (ttpResult_lt_mod t)]
  exact Int.toNat_of_nonneg (ttpResult_nonneg t)

/-- `wordOfInt (uNorm i)` vanishes iff the residue is `0`. -/
theorem wordOfInt_uNorm_eq_zero_iff (i : Int) :
    EVM.wordOfInt (normalizeInt uint256T i) = ⟨0⟩ ↔ normalizeInt uint256T i = 0 := by
  constructor
  · intro h
    have ht := congrArg UInt256.toNat h
    rw [wordOfInt_toNat] at ht
    have hmod : normalizeInt uint256T i % Int.ofNat EVM.wordModulus =
        normalizeInt uint256T i :=
      Int.emod_eq_of_lt (uNorm_nonneg i) (uNorm_lt_mod i)
    rw [hmod] at ht
    have hnn := uNorm_nonneg i
    have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
    rw [h0] at ht
    omega
  · intro h; rw [h]; rfl

/-- `wordOfInt`-to-`ofNat` for the literals used by the generated code. -/
theorem wordOfInt_ofNat (n : Nat) (h : n < 2 ^ 256) :
    (UInt256.ofNat n : UInt256) = EVM.wordOfInt (Int.ofNat n) := by
  apply u256_inj
  rw [wordOfInt_toNat]
  show (UInt256.ofNat n).toNat =
      Int.toNat (Int.ofNat n % Int.ofNat EVM.wordModulus)
  rw [Int.emod_eq_of_lt]
  · show (UInt256.ofNat n).toNat = n
    exact ulit_toNat' n h
  · exact Int.natCast_nonneg n
  · show Int.ofNat n < Int.ofNat (2 ^ 256)
    exact Int.ofNat_lt.mpr h

/-- Unsigned `word`-division bridge: `div (wordOfInt a) (wordOfInt b) = wordOfInt (a/b)`
    for nonnegative bounded `a`, `b`. -/
theorem ttpDiv_word {a b : Int} (ha : 0 ≤ a) (haM : a < Int.ofNat EVM.wordModulus)
    (hb : 0 ≤ b) (hbM : b < Int.ofNat EVM.wordModulus) :
    UInt256.div (EVM.wordOfInt a) (EVM.wordOfInt b) = EVM.wordOfInt (a / b) := by
  have hqa : a.toNat < EVM.wordModulus := by
    have h1 : Int.ofNat a.toNat = a := Int.toNat_of_nonneg ha
    have h2 : Int.ofNat a.toNat < Int.ofNat EVM.wordModulus := by rw [h1]; exact haM
    exact Int.ofNat_lt.mp h2
  have hqb : b.toNat < EVM.wordModulus := by
    have h1 : Int.ofNat b.toNat = b := Int.toNat_of_nonneg hb
    have h2 : Int.ofNat b.toNat < Int.ofNat EVM.wordModulus := by rw [h1]; exact hbM
    exact Int.ofNat_lt.mp h2
  have hwa : EVM.wordOfInt a = UInt256.ofNat a.toNat := by
    apply u256_inj
    rw [wordOfInt_toNat, Int.emod_eq_of_lt ha haM, ulit_toNat' a.toNat hqa]
  have hwb : EVM.wordOfInt b = UInt256.ofNat b.toNat := by
    apply u256_inj
    rw [wordOfInt_toNat, Int.emod_eq_of_lt hb hbM, ulit_toNat' b.toNat hqb]
  rw [hwa, hwb]
  have hdv : a / b = Int.ofNat (a.toNat / b.toNat) := by
    nth_rewrite 1 [show a = Int.ofNat a.toNat from (Int.toNat_of_nonneg ha).symm]
    nth_rewrite 1 [show b = Int.ofNat b.toNat from (Int.toNat_of_nonneg hb).symm]
    exact Int.ofNat_ediv_ofNat.symm
  rw [hdv]
  apply u256_inj
  rw [udiv_toNat, ulit_toNat' _ hqa, ulit_toNat' _ hqb, wordOfInt_toNat]
  have e3 : Int.ofNat (a.toNat / b.toNat) % Int.ofNat EVM.wordModulus =
      Int.ofNat (a.toNat / b.toNat) :=
    Int.emod_eq_of_lt (Int.ofNat_nonneg _)
      (Int.ofNat_lt.mpr (lt_of_le_of_lt (Nat.div_le_self a.toNat b.toNat) hqa))
  rw [e3]
  rfl

theorem tickToPriceBody_eq : tickToPriceTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "__calldata" (some .bytes) (.env .msgData),
     .require (.binary .lt
        (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)),
     .internalCall "tickToPrice_body" [.var "tick"] "__r",
     .return [.var "__r"]] := rfl

abbrev tickToPriceBodyDecl : FunctionDecl := contract.functions[1]!

/-- `tickToPrice_body`'s spec body as emitted. -/
theorem t2pBodyDecl_body_eq : tickToPriceBodyDecl.body =
    [.require (.binary .le (.var "tick") (.intLit 6744)),
     .internalCall "wExp_body"
       [.cast (.binary .mul (.intLit 4987541511039073)
         (.cast (.binary .sub (.intLit 3372)
           (.cast (.var "tick") sint256S)) sint256S)) sint256S] "__c0",
     .letDecl "__d1" none
       (.cast (.binary .div
         (.cast (.binary .add (.intLit 1000000000000000000000000000000000000)
           (.binary .div
             (.binary .sub
               (.cast (.binary .add (.intLit 1000000000000000000) (.var "__c0")) uint256S)
               (.intLit 1)) (.intLit 2))) uint256S)
         (.cast (.binary .add (.intLit 1000000000000000000) (.var "__c0")) uint256S))
         uint256S),
     .letDecl "__d2" none
       (.cast (.binary .div
         (.cast (.binary .add (.var "__d1")
           (.binary .div (.binary .sub (.intLit 100000000000) (.intLit 1)) (.intLit 2)))
           uint256S) (.intLit 100000000000)) uint256S),
     .return [.cast (.binary .mul (.var "__d2") (.intLit 100000000000)) uint256S]] :=
  rfl

/-! ### Selector arm: decode lemmas -/

/-- The `uint256` calldata decodes to `tick := ofNat word` when a full word follows the
    selector and the calldata is under the huge-length bound. -/
theorem t2pDecode_ok {cd : ByteArray} (hsz36 : 36 ≤ cd.size) (hmax : cd.size < 2 ^ 255 + 4) :
    config.externalABI.decodeCalldata? (tickToPriceTransition.params.map Param.name)
      (transitionSignature tickToPriceTransition).paramTypes cd =
      some ((∅ : Store).insert "tick"
        (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  show decodeCalldataWithMode .modern _ _ cd = _
  show decodeCalldata ["tick"] [.elem (.int (.uint ⟨256, by decide⟩))] cd = _
  exact decodeCalldata_uint256_ok hsz36 hmax

/-- Decode fails when the `uint256` word is missing or the calldata is huge. -/
theorem t2pDecode_none {cd : ByteArray} (hsz4 : 4 ≤ cd.size)
    (h : cd.size < 36 ∨ 2 ^ 255 + 4 ≤ cd.size) :
    config.externalABI.decodeCalldata? (tickToPriceTransition.params.map Param.name)
      (transitionSignature tickToPriceTransition).paramTypes cd = none := by
  show decodeCalldataWithMode .modern _ _ cd = _
  show decodeCalldata ["tick"] [.elem (.int (.uint ⟨256, by decide⟩))] cd = _
  rcases h with hs | hb
  · exact decodeCalldata_uint256_none_short hs
  · exact decodeCalldata_uint256_none_huge hb

/-! ### Stele-side body

`tickToPrice_body`: `require tick ≤ 6744`, internal `wExp_body` call on
`int256(LN * int256(3372 - int256(tick)))`, then `__d1`/`__d2` post-processing. -/

/-- The `wExp_body` argument expression evaluates to `ttpArg t` when `t ≤ 6744`. -/
theorem t2pArg_eval {cfg : Config} {caller : Frame} {evm : EVM.State}
    {t : Nat} (ht : t ≤ 6744)
    (hloc : caller.locals.get? "tick" = some (.int (Int.ofNat t))) :
    evalExpr? cfg caller evm
      (.cast (.binary .mul (.intLit 4987541511039073)
        (.cast (.binary .sub (.intLit 3372)
          (.cast (.var "tick") sint256S)) sint256S)) sint256S) =
      .ok (.int (ttpArg t)) := by
  simp only [evalExpr?, hloc, evalBinaryOp?, castValue_int,
    EvalResult.bind, bind, EvalResult.ofOption]
  have ht0 : (0 : Int) ≤ Int.ofNat t := Int.ofNat_nonneg t
  have htt : Int.ofNat t ≤ 6744 := Int.ofNat_le.mpr ht
  have ht1 : normalizeInt sint256T (Int.ofNat t) = Int.ofNat t :=
    sintNorm_of_mem _ (by omega) (by omega)
  have ht2 : normalizeInt sint256T (3372 - Int.ofNat t) = 3372 - Int.ofNat t :=
    sintNorm_of_mem _ (by omega) (by omega)
  rw [ht1, ht2]
  have ht3 : normalizeInt sint256T (4987541511039073 * (3372 - Int.ofNat t)) =
      4987541511039073 * (3372 - Int.ofNat t) := by
    have hb := ttpArg_bound ht
    show normalizeInt sint256T (ttpArg t) = ttpArg t
    exact sintNorm_of_mem _ (le_of_lt hb.1) hb.2
  rw [ht3]
  rfl

/-- The resumed frame after the `wExp_body` internal call inserts
    `__c0 ↦ wExpVal (ttpArg t)`. -/
theorem t2pBodyStele (cfg : Config) (caller : Frame) (evm : EVM.State)
    (t : Nat) (ht : t ≤ 6744)
    (hcontract : caller.contract = contract)
    (hloc : caller.locals.get? "tick" = some (.int (Int.ofNat t)))
    (hbound : ttpArg t < 0 → wExpPos (-ttpArg t) ≠ 0)
    (hden : ttpDen (wExpVal (ttpArg t)) ≠ 0) :
    ∃ stele', ExecFuncBody cfg caller evm tickToPriceBodyDecl.body
      (.returned stele' evm (some [.int (ttpResult t)])) := by
  rw [t2pBodyDecl_body_eq]
  -- require `tick ≤ 6744`
  have hreq : evalExpr? cfg caller evm
      (.binary .le (.var "tick") (.intLit 6744)) = .ok (.bool true) := by
    simp only [evalExpr?, hloc, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    rw [show decide (Int.ofNat t ≤ (6744 : Int)) = true from
      decide_eq_true_iff.mpr (Int.ofNat_le.mpr ht)]
  have hargs : evalExprs? cfg caller evm
      [.cast (.binary .mul (.intLit 4987541511039073)
        (.cast (.binary .sub (.intLit 3372)
          (.cast (.var "tick") sint256S)) sint256S)) sint256S] =
      .ok [.int (ttpArg t)] :=
    evalExprs?_singleton (t2pArg_eval ht hloc)
  have hlookup : lookupCallable? caller.contract "wExp_body" =
      some wExpBodyDecl.toCallable := by rw [hcontract]; rfl
  have hbind : bindParams? wExpBodyDecl.params [.int (ttpArg t)] =
      some ((∅ : Store).insert "x" (.int (ttpArg t))) := rfl
  have hloc' : ({caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      : Frame).locals.get? "x" = some (.int (ttpArg t)) :=
    store_get_self _ _ _
  have hcontract' : ({caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      : Frame).contract = contract := hcontract
  obtain ⟨calleeStele, hcallee⟩ := wExpBodyStele cfg
      {caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      evm (ttpArg t) (ttpArg_ne_min ht) (ttpArg_bound ht).1 hcontract' hloc' hbound
  have hic := internalCallFunctionReturn (name := "wExp_body") (retVar := "__c0")
      (callee := wExpBodyDecl)
      (locals := (∅ : Store).insert "x" (.int (ttpArg t))) hargs hlookup hbind hcallee
  let resumed : Frame := resumeAfterInternalCall caller "__c0"
      (some [.int (wExpVal (ttpArg t))])
  refine ⟨⟨caller.contract, (resumed.locals.insert "__d1"
      (.int (ttpD1 (wExpVal (ttpArg t))))).insert "__d2"
      (.int (ttpD2 (wExpVal (ttpArg t)))), caller.immutables⟩,
      ExecFuncBody.execBlockRet ?_⟩
  have b0 := ABlock.requireStep (ABlock.start (cfg := cfg) (evm := evm)
      (stele := caller) (stmts := tickToPriceBodyDecl.body)) hreq
  apply b0.run
  refine ExecBlock.consNormal hic ?_
  -- __d1
  have hd1 : evalExpr? cfg (resumeAfterInternalCall caller "__c0"
      (some [.int (wExpVal (ttpArg t))])) evm
      (.cast (.binary .div
        (.cast (.binary .add (.intLit 1000000000000000000000000000000000000)
          (.binary .div
            (.binary .sub
              (.cast (.binary .add (.intLit 1000000000000000000) (.var "__c0")) uint256S)
              (.intLit 1)) (.intLit 2))) uint256S)
        (.cast (.binary .add (.intLit 1000000000000000000) (.var "__c0")) uint256S))
        uint256S) = .ok (.int (ttpD1 (wExpVal (ttpArg t)))) := by
    have hc0 : (resumeAfterInternalCall caller "__c0"
        (some [.int (wExpVal (ttpArg t))])).locals.get? "__c0" =
        some (.int (wExpVal (ttpArg t))) := by
      show (caller.locals.insert "__c0" (.int (wExpVal (ttpArg t)))).get? "__c0" = _
      exact store_get_self _ _ _
    simp only [evalExpr?, hc0, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_neg (by decide : (2 : Int) ≠ 0)]
    simp only [castValue_int]
    rw [if_neg (show normalizeInt uint256T
          (1000000000000000000 + wExpVal (ttpArg t)) ≠ 0 from hden)]
    dsimp only []
    simp only [castValue_int]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl hd1) ?_
  -- __d2
  have hd2 : evalExpr? cfg {resumeAfterInternalCall caller "__c0"
      (some [.int (wExpVal (ttpArg t))]) with
        locals := (resumeAfterInternalCall caller "__c0"
          (some [.int (wExpVal (ttpArg t))])).locals.insert "__d1"
          (.int (ttpD1 (wExpVal (ttpArg t))))} evm
      (.cast (.binary .div
        (.cast (.binary .add (.var "__d1")
          (.binary .div (.binary .sub (.intLit 100000000000) (.intLit 1)) (.intLit 2)))
          uint256S) (.intLit 100000000000)) uint256S) =
      .ok (.int (ttpD2 (wExpVal (ttpArg t)))) := by
    have hd1l : ({resumeAfterInternalCall caller "__c0"
        (some [.int (wExpVal (ttpArg t))]) with
          locals := (resumeAfterInternalCall caller "__c0"
            (some [.int (wExpVal (ttpArg t))])).locals.insert "__d1"
            (.int (ttpD1 (wExpVal (ttpArg t))))} : Frame).locals.get? "__d1" =
        some (.int (ttpD1 (wExpVal (ttpArg t)))) :=
      store_get_self _ _ _
    simp only [evalExpr?, hd1l, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_neg (by decide : (2 : Int) ≠ 0)]
    simp only [castValue_int]
    rw [if_neg (by decide : (100000000000 : Int) ≠ 0)]
    dsimp only []
    simp only [castValue_int]
    show EvalResult.ok (Value.int (normalizeInt uint256T
      (normalizeInt uint256T (ttpD1 (wExpVal (ttpArg t)) +
        (100000000000 - 1) / 2) / 100000000000))) =
      EvalResult.ok (Value.int (ttpD2 (wExpVal (ttpArg t))))
    have hhalf : (100000000000 - 1) / 2 = (49999999999 : Int) := by decide
    rw [hhalf]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl hd2) ?_
  -- return
  have hret : evalExpr? cfg ({resumeAfterInternalCall caller "__c0"
      (some [.int (wExpVal (ttpArg t))]) with
        locals := ((resumeAfterInternalCall caller "__c0"
          (some [.int (wExpVal (ttpArg t))])).locals.insert "__d1"
          (.int (ttpD1 (wExpVal (ttpArg t))))).insert "__d2"
          (.int (ttpD2 (wExpVal (ttpArg t))))}) evm
      (.cast (.binary .mul (.var "__d2") (.intLit 100000000000)) uint256S) =
      .ok (.int (ttpResult t)) := by
    have hd2l : ({resumeAfterInternalCall caller "__c0"
        (some [.int (wExpVal (ttpArg t))]) with
          locals := ((resumeAfterInternalCall caller "__c0"
            (some [.int (wExpVal (ttpArg t))])).locals.insert "__d1"
            (.int (ttpD1 (wExpVal (ttpArg t))))).insert "__d2"
            (.int (ttpD2 (wExpVal (ttpArg t))))} : Frame).locals.get? "__d2" =
        some (.int (ttpD2 (wExpVal (ttpArg t)))) :=
      store_get_self _ _ _
    simp only [evalExpr?, hd2l, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rfl
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret))

/-- `tickToPrice_body` reverts at `require tick ≤ 6744` when `t > 6744`. -/
theorem t2pBodyStele_req (cfg : Config) (caller : Frame) (evm : EVM.State)
    (t : Nat) (ht : ¬ t ≤ 6744)
    (hloc : caller.locals.get? "tick" = some (.int (Int.ofNat t))) :
    ExecFuncBody cfg caller evm tickToPriceBodyDecl.body .reverted := by
  rw [t2pBodyDecl_body_eq]
  have hreq : evalExpr? cfg caller evm
      (.binary .le (.var "tick") (.intLit 6744)) = .ok (.bool false) := by
    simp only [evalExpr?, hloc, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    rw [show decide (Int.ofNat t ≤ (6744 : Int)) = false from
      decide_eq_false_iff_not.mpr (by
        intro hc
        exact ht (Int.ofNat_le.mp hc))]
  exact ExecFuncBody.execBlockRevert (ABlock.start.requireRevert hreq)

/-- `tickToPrice_body` reverts via `internalCallFunctionRevert` when the inner
    `wExp_body` call reverts (`wExpPos (-arg) = 0` divisor). -/
theorem t2pBodyStele_divZero (cfg : Config) (caller : Frame) (evm : EVM.State)
    (t : Nat) (ht : t ≤ 6744)
    (hcontract : caller.contract = contract)
    (hloc : caller.locals.get? "tick" = some (.int (Int.ofNat t)))
    (hneg : ttpArg t < 0) (hz : wExpPos (-ttpArg t) = 0) :
    ExecFuncBody cfg caller evm tickToPriceBodyDecl.body .reverted := by
  rw [t2pBodyDecl_body_eq]
  have hreq : evalExpr? cfg caller evm
      (.binary .le (.var "tick") (.intLit 6744)) = .ok (.bool true) := by
    simp only [evalExpr?, hloc, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    rw [show decide (Int.ofNat t ≤ (6744 : Int)) = true from
      decide_eq_true_iff.mpr (Int.ofNat_le.mpr ht)]
  have hargs : evalExprs? cfg caller evm
      [.cast (.binary .mul (.intLit 4987541511039073)
        (.cast (.binary .sub (.intLit 3372)
          (.cast (.var "tick") sint256S)) sint256S)) sint256S] =
      .ok [.int (ttpArg t)] :=
    evalExprs?_singleton (t2pArg_eval ht hloc)
  have hlookup : lookupCallable? caller.contract "wExp_body" =
      some wExpBodyDecl.toCallable := by rw [hcontract]; rfl
  have hbind : bindParams? wExpBodyDecl.params [.int (ttpArg t)] =
      some ((∅ : Store).insert "x" (.int (ttpArg t))) := rfl
  have hloc' : ({caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      : Frame).locals.get? "x" = some (.int (ttpArg t)) :=
    store_get_self _ _ _
  have hcontract' : ({caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      : Frame).contract = contract := hcontract
  have hcallee := wExpBodyStele_divZero cfg
      {caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      evm (ttpArg t) hneg (ttpArg_ne_min ht) (ttpArg_bound ht).1 hcontract' hloc' hz
  have hic := internalCallFunctionRevert (name := "wExp_body") (retVar := "__c0")
      (callee := wExpBodyDecl)
      (locals := (∅ : Store).insert "x" (.int (ttpArg t))) hargs hlookup hbind hcallee
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreq) (ExecBlock.consRevert hic)

/-- `tickToPrice_body` reverts at `__d1`'s `letDecl` when the denominator is zero. -/
theorem t2pBodyStele_denZero (cfg : Config) (caller : Frame) (evm : EVM.State)
    (t : Nat) (ht : t ≤ 6744)
    (hcontract : caller.contract = contract)
    (hloc : caller.locals.get? "tick" = some (.int (Int.ofNat t)))
    (hbound : ttpArg t < 0 → wExpPos (-ttpArg t) ≠ 0)
    (hdz : ttpDen (wExpVal (ttpArg t)) = 0) :
    ExecFuncBody cfg caller evm tickToPriceBodyDecl.body .reverted := by
  rw [t2pBodyDecl_body_eq]
  have hreq : evalExpr? cfg caller evm
      (.binary .le (.var "tick") (.intLit 6744)) = .ok (.bool true) := by
    simp only [evalExpr?, hloc, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    rw [show decide (Int.ofNat t ≤ (6744 : Int)) = true from
      decide_eq_true_iff.mpr (Int.ofNat_le.mpr ht)]
  have hargs : evalExprs? cfg caller evm
      [.cast (.binary .mul (.intLit 4987541511039073)
        (.cast (.binary .sub (.intLit 3372)
          (.cast (.var "tick") sint256S)) sint256S)) sint256S] =
      .ok [.int (ttpArg t)] :=
    evalExprs?_singleton (t2pArg_eval ht hloc)
  have hlookup : lookupCallable? caller.contract "wExp_body" =
      some wExpBodyDecl.toCallable := by rw [hcontract]; rfl
  have hbind : bindParams? wExpBodyDecl.params [.int (ttpArg t)] =
      some ((∅ : Store).insert "x" (.int (ttpArg t))) := rfl
  have hloc' : ({caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      : Frame).locals.get? "x" = some (.int (ttpArg t)) :=
    store_get_self _ _ _
  have hcontract' : ({caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      : Frame).contract = contract := hcontract
  obtain ⟨calleeStele, hcallee⟩ := wExpBodyStele cfg
      {caller with locals := (∅ : Store).insert "x" (.int (ttpArg t))}
      evm (ttpArg t) (ttpArg_ne_min ht) (ttpArg_bound ht).1 hcontract' hloc' hbound
  have hic := internalCallFunctionReturn (name := "wExp_body") (retVar := "__c0")
      (callee := wExpBodyDecl)
      (locals := (∅ : Store).insert "x" (.int (ttpArg t))) hargs hlookup hbind hcallee
  have hd1rev : evalExpr? cfg (resumeAfterInternalCall caller "__c0"
      (some [.int (wExpVal (ttpArg t))])) evm
      (.cast (.binary .div
        (.cast (.binary .add (.intLit 1000000000000000000000000000000000000)
          (.binary .div
            (.binary .sub
              (.cast (.binary .add (.intLit 1000000000000000000) (.var "__c0")) uint256S)
              (.intLit 1)) (.intLit 2))) uint256S)
        (.cast (.binary .add (.intLit 1000000000000000000) (.var "__c0")) uint256S))
        uint256S) = .revert := by
    have hc0 : (resumeAfterInternalCall caller "__c0"
        (some [.int (wExpVal (ttpArg t))])).locals.get? "__c0" =
        some (.int (wExpVal (ttpArg t))) := by
      show (caller.locals.insert "__c0" (.int (wExpVal (ttpArg t)))).get? "__c0" = _
      exact store_get_self _ _ _
    simp only [evalExpr?, hc0, evalBinaryOp?, castValue_int,
      EvalResult.bind, bind, EvalResult.ofOption]
    rw [if_neg (by decide : (2 : Int) ≠ 0)]
    simp only [castValue_int]
    rw [if_pos (show normalizeInt uint256T
          (1000000000000000000 + wExpVal (ttpArg t)) = 0 from hdz)]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.consNormal hic (ExecBlock.consRevert (ExecStmt.letDeclRevert hd1rev))

/-- `tickToPrice(uint256)`'s spec body returns `some [.int (ttpResult t)]` whenever
    `tick ↦ ofNat t` is in scope with `t ≤ 6744`, the inner `wExp` divisor is nonzero,
    and the `__d1` denominator is nonzero. -/
theorem t2pTransitionReturns (evm : EVM.State) (t : Nat) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ht : t ≤ 6744)
    (hbound : ttpArg t < 0 → wExpPos (-ttpArg t) ≠ 0)
    (hden : ttpDen (wExpVal (ttpArg t)) ≠ 0)
    (hx : callargs.get? "tick" = some (.int (Int.ofNat t))) :
    ∃ cs, ExecTransitionBody config contract evm callargs tickToPriceTransition.body
      (.returned cs evm (some [.int (ttpResult t)])) := by
  rw [tickToPriceBody_eq]
  let cd : ByteArray := evm.executionEnv.calldata
  have hx' : (callargs.insert "__calldata" (.bytes cd)).get? "tick" =
      some (.int (Int.ofNat t)) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "tick") = false)]
    exact hx
  have hargs : evalExprs? config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } evm
      [.var "tick"] = .ok [.int (Int.ofNat t)] := by
    simp only [evalExprs?, evalExpr?, hx', EvalResult.bind, bind, EvalResult.ofOption, pure]
  have hlookup : lookupCallable? contract "tickToPrice_body" =
      some tickToPriceBodyDecl.toCallable := rfl
  have hbind : bindParams? tickToPriceBodyDecl.params [.int (Int.ofNat t)] =
      some ((∅ : Store).insert "tick" (.int (Int.ofNat t))) := rfl
  have hcontract' : (⟨contract, callargs.insert "__calldata" (.bytes cd), (∅ : Store)⟩
      : Frame).contract = contract := rfl
  have hloc' : (⟨contract, (∅ : Store).insert "tick" (.int (Int.ofNat t)), (∅ : Store)⟩
      : Frame).locals.get? "tick" = some (.int (Int.ofNat t)) :=
    store_get_self _ _ _
  obtain ⟨cs, hb⟩ := t2pBodyStele config
      { contract := contract,
        locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)), immutables := ∅ }
      evm t ht hcontract' hloc' hbound hden
  have hic := internalCallFunctionReturn (name := "tickToPrice_body") (retVar := "__r")
      (args := [.var "tick"]) (argVals := [.int (Int.ofNat t)])
      (locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)))
      (callee := tickToPriceBodyDecl) hargs hlookup hbind hb
  let resumed : Frame := resumeAfterInternalCall
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } "__r"
      (some [.int (ttpResult t)])
  have hres : resumed.locals.get? "__r" = some (.int (ttpResult t)) := by
    show ((callargs.insert "__calldata" (.bytes cd)).insert "__r"
        (collapseReturns [.int (ttpResult t)])).get? "__r" = _
    rw [show collapseReturns [.int (ttpResult t)] = .int (ttpResult t) from rfl]
    exact store_get_self _ _ _
  have hret : evalExpr? config resumed evm (.var "__r") = .ok (.int (ttpResult t)) := by
    simp only [evalExpr?, hres, EvalResult.bind, bind, EvalResult.ofOption, pure]
  refine ⟨⟨contract, resumed.locals, ∅⟩, ExecFuncBody.execBlockRet ?_⟩
  have blk : ExecBlock config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ }
      evm [Stmt.internalCall "tickToPrice_body" [.var "tick"] "__r",
           Stmt.return [.var "__r"]]
      (.returned resumed evm (some [.int (ttpResult t)])) :=
    ExecBlock.consNormal hic
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret)))
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireStep
      (evalCalldataLen_true (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen) |>.run blk

/-- `tickToPrice(uint256)`'s spec body reverts whenever the callee body does. -/
theorem t2pTransitionReverts_call (evm : EVM.State) (t : Nat) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrev : ExecFuncBody config
      { contract := contract,
        locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)), immutables := ∅ }
      evm tickToPriceBodyDecl.body .reverted)
    (hx : callargs.get? "tick" = some (.int (Int.ofNat t))) :
    ExecTransitionBody config contract evm callargs tickToPriceTransition.body
      .reverted := by
  rw [tickToPriceBody_eq]
  let cd : ByteArray := evm.executionEnv.calldata
  have hx' : (callargs.insert "__calldata" (.bytes cd)).get? "tick" =
      some (.int (Int.ofNat t)) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "tick") = false)]
    exact hx
  have hargs : evalExprs? config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } evm
      [.var "tick"] = .ok [.int (Int.ofNat t)] := by
    simp only [evalExprs?, evalExpr?, hx', EvalResult.bind, bind, EvalResult.ofOption, pure]
  have hlookup : lookupCallable? contract "tickToPrice_body" =
      some tickToPriceBodyDecl.toCallable := rfl
  have hbind : bindParams? tickToPriceBodyDecl.params [.int (Int.ofNat t)] =
      some ((∅ : Store).insert "tick" (.int (Int.ofNat t))) := rfl
  have hic := internalCallFunctionRevert (name := "tickToPrice_body") (retVar := "__r")
      (args := [.var "tick"]) (argVals := [.int (Int.ofNat t)])
      (locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)))
      (callee := tickToPriceBodyDecl) hargs hlookup hbind hrev
  refine ExecFuncBody.execBlockRevert ?_
  have blk : ExecBlock config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ }
      evm [Stmt.internalCall "tickToPrice_body" [.var "tick"] "__r",
           Stmt.return [.var "__r"]]
      .reverted := ExecBlock.consRevert hic
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireStep
      (evalCalldataLen_true (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen) |>.run blk

/-- `tickToPrice(uint256)`'s spec body reverts at the calldata-size require when
    the calldata is too large to be decoded. -/
theorem t2pTransitionReverts_len (evm : EVM.State) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : 2 ^ 255 + 4 ≤ evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm callargs tickToPriceTransition.body
      .reverted := by
  rw [tickToPriceBody_eq]
  refine ExecFuncBody.execBlockRevert ?_
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireRevert
      (evalCalldataLen_false (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen)

/-! ### EVM-side trace

Arm entry pc 359 (nonpayable + size guards + `calldataWord 4` load → pc 476 range
check).  `tick ≤ 6744` enters the body at pc 486 which computes
`warg := mul LN (sub 3372 tickw)` and calls the shared wExp tail `591/636/610/617`;
the `tickToPrice` post-processing lives at `523/446/453/570`. -/

/-- `mul (ofNat LN) (sub (ofNat 3372) tickw)` is `wordOfInt (ttpArg t)` when
    `tickw.toNat = t`. -/
theorem ttpArg_word {tw : UInt256} {t : Nat} (ht : t = tw.toNat) :
    UInt256.mul (UInt256.ofNat 4987541511039073)
        (UInt256.sub (UInt256.ofNat 3372) tw) = EVM.wordOfInt (ttpArg t) := by
  have htw : tw = EVM.wordOfInt (Int.ofNat t) := by
    rw [ht]
    have e : EVM.wordOfInt (Int.ofNat tw.toNat) = tw := by
      rw [show EVM.wordOfInt (Int.ofNat tw.toNat) = UInt256.ofNat tw.toNat from rfl]
      exact u256_ofNat_toNat tw
    exact e.symm
  rw [htw, wordOfInt_ofNat 4987541511039073 (by decide),
      wordOfInt_ofNat 3372 (by decide), wordOfInt_sub_of, wordOfInt_mul_of]
  rfl

/-- `signed` of the wExp argument word is `ttpArg t` for `t ≤ 6744`. -/
theorem ttpArg_signed {tw : UInt256} {t : Nat} (ht : t = tw.toNat) (hle : t ≤ 6744) :
    EVM.signed (UInt256.mul (UInt256.ofNat 4987541511039073)
        (UInt256.sub (UInt256.ofNat 3372) tw)) = ttpArg t := by
  rw [ttpArg_word ht, signed_wordOfInt]
  show normalizeInt sint256T (ttpArg t) = ttpArg t
  exact ttpArg_sintNorm hle

/-- `1e18 + wordOfInt c0` is `wordOfInt (ttpDen c0)`. -/
theorem ttpDen_word (c0 : Int) :
    UInt256.ofNat 1000000000000000000 + EVM.wordOfInt c0 =
      EVM.wordOfInt (ttpDen c0) := by
  rw [wordOfInt_ofNat _ (by decide), ← wordOfInt_add]
  show EVM.wordOfInt (Int.ofNat 1000000000000000000 + c0) =
      EVM.wordOfInt (normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat 1000000000000000000 + c0))
  rw [wordOfInt_uintNorm]

/-- Logical shift-right-by-one of `wordOfInt j` is `wordOfInt (j / 2)` for `j ≥ 0`. -/
theorem ushr1_word {j : Int} (hj : 0 ≤ j) (hjM : j < Int.ofNat EVM.wordModulus) :
    UInt256.shiftRight (EVM.wordOfInt j) (UInt256.ofNat 1) = EVM.wordOfInt (j / 2) := by
  apply u256_inj
  show (UInt256.shiftRight (EVM.wordOfInt j) (UInt256.ofNat 1)).toNat =
      (EVM.wordOfInt (j / 2)).toNat
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg (by decide : ¬ ((UInt256.ofNat 1 : UInt256).val ≥ 256)),
      Fin.shiftRight_val, Nat.shiftRight_eq_div_pow,
      show (UInt256.ofNat 1 : UInt256).val.val = 1 from
        ulit_toNat' 1 (by decide : (1:Nat) < UInt256.size), pow_one]
  show (EVM.wordOfInt j).toNat / 2 = (EVM.wordOfInt (j / 2)).toNat
  rw [wordOfInt_toNat, wordOfInt_toNat, Int.emod_eq_of_lt hj hjM,
      Int.emod_eq_of_lt (Int.ediv_nonneg hj (by decide)) (by
        have hle : j / 2 ≤ j := by omega
        exact lt_of_le_of_lt hle hjM)]
  have hdv : j / 2 = Int.ofNat (j.toNat / 2) := by
    nth_rewrite 1 [show j = Int.ofNat j.toNat from (Int.toNat_of_nonneg hj).symm]
    exact Int.ofNat_ediv_ofNat.symm
  rw [hdv]
  rfl

/-- The EVM `523/446/453/570` post-processing words collapse to
    `wordOfInt (ttpResult t)`. -/
theorem ttpResult_word (t : Nat) (hden : ttpDen (wExpVal (ttpArg t)) ≠ 0) :
    UInt256.mul
        (UInt256.div
          ((UInt256.div
            (UInt256.ofNat 1000000000000000000000000000000000000 +
              UInt256.shiftRight
                (EVM.wordOfInt (wExpVal (ttpArg t)) + UInt256.ofNat 999999999999999999)
                (UInt256.ofNat 1))
            (UInt256.ofNat 1000000000000000000 + EVM.wordOfInt (wExpVal (ttpArg t)))) +
            UInt256.ofNat 49999999999)
          (UInt256.ofNat 100000000000))
        (UInt256.ofNat 100000000000) = EVM.wordOfInt (ttpResult t) := by
  set c0 := wExpVal (ttpArg t)
  set D := ttpDen c0
  have hD0 : 0 ≤ D := uNorm_nonneg (1000000000000000000 + c0)
  have hDM : D < Int.ofNat EVM.wordModulus := uNorm_lt_mod (1000000000000000000 + c0)
  have hD1 : 1 ≤ D := by
    have hne : D ≠ 0 := hden
    omega
  -- denominator word
  have hDw : UInt256.ofNat 1000000000000000000 + EVM.wordOfInt c0 =
      EVM.wordOfInt D := ttpDen_word c0
  -- shift-word:  c0w + (1e18 - 1)  >>> 1
  have hpre : EVM.wordOfInt c0 + UInt256.ofNat 999999999999999999 =
      EVM.wordOfInt (D - 1) := by
    rw [wordOfInt_ofNat 999999999999999999 (by decide), ← wordOfInt_add]
    show EVM.wordOfInt (c0 + Int.ofNat 999999999999999999) = EVM.wordOfInt (D - 1)
    apply wordOfInt_cong
    show (c0 + 999999999999999999) % Int.ofNat EVM.wordModulus =
        (ttpDen c0 - 1) % Int.ofNat EVM.wordModulus
    rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]
    have hmod : ttpDen c0 =
        (1000000000000000000 + c0) % (2 ^ 256 : Int) := rfl
    omega
  have hshr : UInt256.shiftRight (EVM.wordOfInt c0 + UInt256.ofNat 999999999999999999)
      (UInt256.ofNat 1) = EVM.wordOfInt ((D - 1) / 2) := by
    rw [hpre]
    exact ushr1_word (by omega) (by omega)
  -- numerator word
  have hNw : UInt256.ofNat 1000000000000000000000000000000000000 +
      UInt256.shiftRight (EVM.wordOfInt c0 + UInt256.ofNat 999999999999999999)
        (UInt256.ofNat 1) =
      EVM.wordOfInt (normalizeInt uint256T
        (1000000000000000000000000000000000000 + (D - 1) / 2)) := by
    rw [hshr, wordOfInt_ofNat _ (by decide), ← wordOfInt_add]
    show EVM.wordOfInt (Int.ofNat 1000000000000000000000000000000000000 + (D - 1) / 2) = _
    rw [wordOfInt_uintNorm]
    rfl
  -- __d1 word
  have hd1w : UInt256.div
      (UInt256.ofNat 1000000000000000000000000000000000000 +
        UInt256.shiftRight (EVM.wordOfInt c0 + UInt256.ofNat 999999999999999999)
          (UInt256.ofNat 1))
      (UInt256.ofNat 1000000000000000000 + EVM.wordOfInt c0) =
      EVM.wordOfInt (ttpD1 c0) := by
    rw [hNw, hDw]
    have h := ttpDiv_word
      (a := normalizeInt uint256T (1000000000000000000000000000000000000 + (D - 1) / 2))
      (b := D) (uNorm_nonneg _) (uNorm_lt_mod _) hD0 hDM
    rw [h]
    rw [show ttpD1 c0 = normalizeInt uint256T
          (normalizeInt uint256T (1000000000000000000000000000000000000 +
            (ttpDen c0 - 1) / 2) / ttpDen c0) from rfl, wordOfInt_uintNorm]
  -- __d2 word
  have hd2w : UInt256.div (UInt256.div
        (UInt256.ofNat 1000000000000000000000000000000000000 +
          UInt256.shiftRight (EVM.wordOfInt c0 + UInt256.ofNat 999999999999999999)
            (UInt256.ofNat 1))
        (UInt256.ofNat 1000000000000000000 + EVM.wordOfInt c0) +
        UInt256.ofNat 49999999999) (UInt256.ofNat 100000000000) =
      EVM.wordOfInt (ttpD2 c0) := by
    rw [hd1w, wordOfInt_ofNat 49999999999 (by decide), ← wordOfInt_add,
        ← wordOfInt_uintNorm, wordOfInt_ofNat 100000000000 (by decide)]
    have h := ttpDiv_word
      (a := normalizeInt uint256T (ttpD1 c0 + Int.ofNat 49999999999))
      (b := Int.ofNat 100000000000) (uNorm_nonneg _) (uNorm_lt_mod _)
      (Int.ofNat_nonneg _)
      (Int.ofNat_lt.mpr (by decide : (100000000000 : Nat) < EVM.wordModulus))
    rw [h]
    rw [show ttpD2 c0 = normalizeInt uint256T
          (normalizeInt uint256T (ttpD1 c0 + Int.ofNat 49999999999) /
            Int.ofNat 100000000000) from rfl, wordOfInt_uintNorm]
  rw [hd2w, wordOfInt_ofNat 100000000000 (by decide), wordOfInt_mul_of]
  show EVM.wordOfInt (ttpD2 c0 * Int.ofNat 100000000000) = EVM.wordOfInt (ttpResult t)
  rw [show ttpResult t = normalizeInt uint256T (ttpD2 (wExpVal (ttpArg t)) *
      Int.ofNat 100000000000) from rfl, wordOfInt_uintNorm]

/-- The shared `523 → 446 → 453 → 570 → 123` post-processing tail: from the
    `wExpVal (ttpArg t)` result word on top to `RDret` of `ttpResult t`. -/
theorem t2pX_tail {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {t : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hden : ttpDen (wExpVal (ttpArg t)) ≠ 0)
    (rd : RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 523)
      (EVM.wordOfInt (wExpVal (ttpArg t)) :: (UInt256.ofNat 570) ::
        (UInt256.ofNat 49999999999) :: (UInt256.ofNat 100000000000) ::
        (UInt256.ofNat 100000000000) :: (UInt256.ofNat 123) ::
        (UInt256.ofNat 32) :: R)
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty
        (UInt256.ofNat 64).toNat 32)
      aw rdata σ k C) :
    RDret tickLibWrapperBytecode g s0 σ (EVM.wordOfInt (ttpResult t)).toByteArray := by
  have rd523 := tickLibWrapperBlocks.tickLibWrapper_block_523
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_523_stack] at rd523
  -- 446: denominator `1e18 + c0` is nonzero
  have hz : UInt256.isZero (UInt256.ofNat 1000000000000000000 +
      EVM.wordOfInt (wExpVal (ttpArg t))) = ⟨0⟩ := by
    rw [ttpDen_word]
    apply isZero_eq_zero_of_ne
    intro hz'
    exact hden ((wordOfInt_uNorm_eq_zero_iff _).mp hz')
  have rd446 := tickLibWrapperBlocks.tickLibWrapper_block_446_fallthrough
    (by simp only [List.length_cons]; omega) hz rd523
  have rd453 := tickLibWrapperBlocks.tickLibWrapper_block_453
    (by simp only [List.length_cons]; omega) (by jump_dest) rd446
  have rd570 := tickLibWrapperBlocks.tickLibWrapper_block_570
    (by simp only [List.length_cons]; omega) (by jump_dest) rd453
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_570_stack] at rd570
  have hres := ttpResult_word t hden
  rw [hres] at rd570
  have rd123 := tickLibWrapperBlocks.tickLibWrapper_block_123
    (by omega) rd570
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide, dispatchMemLoad64] at rd123
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      show (UInt256.ofNat 32).toNat = 32 from by decide] at rd123
  have hmemsize : ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32).size =
      96 := toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
      (lt_usize _ (by decide)) (by decide)
  rw [toByteArray_write_read_back_of_gap _ _ 128
      (by rw [hmemsize]; exact lt_usize _ (by decide))] at rd123
  exact rd123

/-- `tickToPrice(uint256)` — ordinary path: the body returns
    `(wordOfInt (ttpResult t)).toByteArray`. -/
theorem t2pX_ok {σ σ₀ A I} {g : Sat256} {t : Nat}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 2))
    (ht : t = (calldataWord I.calldata 4).toNat) (hle : t ≤ 6744)
    (hbound : ttpArg t < 0 → wExpPos (-ttpArg t) ≠ 0)
    (hden : ttpDen (wExpVal (ttpArg t)) ≠ 0) :
    RDret tickLibWrapperBytecode g (initState σ σ₀ g A I) σ
      (EVM.wordOfInt (ttpResult t)).toByteArray := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachTickToPriceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_359_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_365_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_377 (by simp) (by jump_dest) rd2
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_377_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  set tw := calldataWord I.calldata 4 with htw
  have hgt : UInt256.gt tw (UInt256.ofNat 6744) = ⟨0⟩ := by
    apply ugt_zero
    rw [ulit_toNat' 6744 (by decide : 6744 < UInt256.size)]
    rw [← ht]
    omega
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_476_fallthrough (by simp) hgt rd3
  have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_486 (by simp) (by jump_dest) rd4
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_486_stack] at rd5
  set warg := UInt256.mul (UInt256.ofNat 4987541511039073)
      (UInt256.sub (UInt256.ofNat 3372) tw) with hwarg
  have hsign : EVM.signed warg = ttpArg t := by
    rw [hwarg]
    exact ttpArg_signed ht hle
  -- shared wExp tail: sign of `warg` decides 591-taken (arg ≥ 0) or 600/610/617.
  have hwarg' : warg = EVM.wordOfInt (ttpArg t) := by rw [hwarg]; exact ttpArg_word ht
  by_cases harg0 : ttpArg t < 0
  · -- negative argument: 591 fallthrough → 600 → 591 → 636 → 610 → 617 → 523
    have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) = ⟨0⟩ := by
      have hneg : EVM.signed warg < 0 := by rw [hsign]; exact harg0
      have hge := toNat_ge_2pow255_of_signed_neg hneg
      have hs0 : UInt256.slt warg ⟨0⟩ = ⟨1⟩ := by
        show UInt256.slt warg (UInt256.ofNat 0) = ⟨1⟩
        exact slt_lit_one_high (a := warg) (m := 0) (by norm_num) hge
      rw [hs0]
      exact isZero_eq_zero_of_ne (by decide)
    have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough (by simp) hslt0 rd5
    have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_600 (by simp)
      (by jump_dest) rd6
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd7
    have hneg' : UInt256.sub ⟨0⟩ warg = EVM.wordOfInt (-ttpArg t) := by
      rw [hwarg', show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, wordOfInt_sub_of]
      exact wordOfInt_cong (by
        rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
    have hslt1 : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩) ≠ ⟨0⟩ := by
      have hs : EVM.signed (UInt256.sub ⟨0⟩ warg) = -ttpArg t := by
        rw [hneg', signed_wordOfInt]
        have hb := ttpArg_bound hle
        show normalizeInt sint256T (-ttpArg t) = -ttpArg t
        exact sintNorm_of_mem _ (by omega) (by omega)
      have hnn : 0 ≤ EVM.signed (UInt256.sub ⟨0⟩ warg) := by rw [hs]; omega
      have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
      have hs0 : UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩ = ⟨0⟩ := by
        show UInt256.slt (UInt256.sub ⟨0⟩ warg) (UInt256.ofNat 0) = ⟨0⟩
        exact slt_lit_zero (a := UInt256.sub ⟨0⟩ warg) (m := 0) (by norm_num)
          (Nat.zero_le _) hlt2
      rw [hs0]
      decide
    have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hslt1
      (by jump_dest) rd7
    have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp)
      (by jump_dest) rd8
    rw [wExp636_stack, hneg', signed_wordOfInt,
        show normalizeInt sint256T (-ttpArg t) = -ttpArg t from
          sintNorm_of_mem _ (by have := ttpArg_bound hle; omega)
            (by have := ttpArg_bound hle; omega)] at rd9
    -- at pc 610, stack `[wordOfInt (wExpPos (-arg)), 523, ...]` — divisor nonzero
    have hz : UInt256.isZero (EVM.wordOfInt (wExpPos (-ttpArg t))) = ⟨0⟩ := by
      exact isZero_eq_zero_of_ne (fun hz' =>
        hbound harg0 ((wordOfInt_wExpPos_eq_zero_iff _).mp hz'))
    have rd10 := tickLibWrapperBlocks.tickLibWrapper_block_610_fallthrough (by simp) hz rd9
    have rd11 := tickLibWrapperBlocks.tickLibWrapper_block_617 (by simp)
      (by jump_dest) rd10
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_617_stack,
      wExpVal_div_word _ harg0] at rd11
    exact t2pX_tail (by simp) hden rd11
  · -- nonnegative argument: 591 taken → 636 → 523
    have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) ≠ ⟨0⟩ := by
      have hnn : 0 ≤ EVM.signed warg := by rw [hsign]; omega
      have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
      have hs0 : UInt256.slt warg ⟨0⟩ = ⟨0⟩ := by
        show UInt256.slt warg (UInt256.ofNat 0) = ⟨0⟩
        exact slt_lit_zero (a := warg) (m := 0) (by norm_num) (Nat.zero_le _) hlt2
      rw [hs0]
      decide
    have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hslt0
      (by jump_dest) rd5
    have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp)
      (by jump_dest) rd6
    rw [wExp636_stack, hwarg', signed_wordOfInt,
        show normalizeInt sint256T (ttpArg t) = ttpArg t from ttpArg_sintNorm hle,
        show wExpPos (ttpArg t) = wExpVal (ttpArg t) from by
          unfold wExpVal; rw [if_neg harg0]] at rd7
    exact t2pX_tail (by simp) hden rd7

/-- `tickToPrice(uint256)` — the `tick > 6744` arm: `476 → 576 → REVERT`. -/
theorem t2pX_rev_gate {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 2))
    (hgt : 6744 < (calldataWord I.calldata 4).toNat) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachTickToPriceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_359_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_365_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_377 (by simp) (by jump_dest) rd2
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_377_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  have hcond : UInt256.gt (calldataWord I.calldata 4) (UInt256.ofNat 6744) ≠ ⟨0⟩ := by
    rw [ugt_one (b := UInt256.ofNat 6744) (by
      rw [ulit_toNat' 6744 (by decide : 6744 < UInt256.size)]; exact hgt)]
    decide
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_476_taken (by simp) hcond
    (by jump_dest) rd3
  exact tickLibWrapperBlocks.tickLibWrapper_block_576 (by simp) rd4

/-- `tickToPrice(uint256)` — negative argument with zero `wExpPos` divisor:
    `610 → 456 → REVERT`. -/
theorem t2pX_divrev {σ σ₀ A I} {g : Sat256} {t : Nat}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 2))
    (ht : t = (calldataWord I.calldata 4).toNat) (hle : t ≤ 6744)
    (hneg : ttpArg t < 0) (hz : wExpPos (-ttpArg t) = 0) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachTickToPriceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_359_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_365_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_377 (by simp) (by jump_dest) rd2
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_377_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  set tw := calldataWord I.calldata 4 with htw
  have hgt : UInt256.gt tw (UInt256.ofNat 6744) = ⟨0⟩ := by
    apply ugt_zero
    rw [ulit_toNat' 6744 (by decide : 6744 < UInt256.size)]
    rw [← ht]
    omega
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_476_fallthrough (by simp) hgt rd3
  have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_486 (by simp) (by jump_dest) rd4
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_486_stack] at rd5
  set warg := UInt256.mul (UInt256.ofNat 4987541511039073)
      (UInt256.sub (UInt256.ofNat 3372) tw) with hwarg
  have hsign : EVM.signed warg = ttpArg t := by
    rw [hwarg]
    exact ttpArg_signed ht hle
  have hwarg' : warg = EVM.wordOfInt (ttpArg t) := by rw [hwarg]; exact ttpArg_word ht
  have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) = ⟨0⟩ := by
    have hn : EVM.signed warg < 0 := by rw [hsign]; exact hneg
    have hge := toNat_ge_2pow255_of_signed_neg hn
    have hs0 : UInt256.slt warg ⟨0⟩ = ⟨1⟩ := by
      show UInt256.slt warg (UInt256.ofNat 0) = ⟨1⟩
      exact slt_lit_one_high (a := warg) (m := 0) (by norm_num) hge
    rw [hs0]
    exact isZero_eq_zero_of_ne (by decide)
  have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough (by simp) hslt0 rd5
  have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_600 (by simp) (by jump_dest) rd6
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd7
  have hneg' : UInt256.sub ⟨0⟩ warg = EVM.wordOfInt (-ttpArg t) := by
    rw [hwarg', show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, wordOfInt_sub_of]
    exact wordOfInt_cong (by
      rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
  have hslt1 : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩) ≠ ⟨0⟩ := by
    have hs : EVM.signed (UInt256.sub ⟨0⟩ warg) = -ttpArg t := by
      rw [hneg', signed_wordOfInt]
      have hb := ttpArg_bound hle
      show normalizeInt sint256T (-ttpArg t) = -ttpArg t
      exact sintNorm_of_mem _ (by omega) (by omega)
    have hnn : 0 ≤ EVM.signed (UInt256.sub ⟨0⟩ warg) := by rw [hs]; omega
    have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
    have hs0 : UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩ = ⟨0⟩ := by
      show UInt256.slt (UInt256.sub ⟨0⟩ warg) (UInt256.ofNat 0) = ⟨0⟩
      exact slt_lit_zero (a := UInt256.sub ⟨0⟩ warg) (m := 0) (by norm_num)
        (Nat.zero_le _) hlt2
    rw [hs0]
    decide
  have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hslt1
    (by jump_dest) rd7
  have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp)
    (by jump_dest) rd8
  rw [wExp636_stack, hneg', signed_wordOfInt,
      show normalizeInt sint256T (-ttpArg t) = -ttpArg t from
        sintNorm_of_mem _ (by have := ttpArg_bound hle; omega)
          (by have := ttpArg_bound hle; omega)] at rd9
  have hz' : UInt256.isZero (EVM.wordOfInt (wExpPos (-ttpArg t))) ≠ ⟨0⟩ := by
    rw [show EVM.wordOfInt (wExpPos (-ttpArg t)) = ⟨0⟩ from
      (wordOfInt_wExpPos_eq_zero_iff _).mpr hz]
    decide
  have rd10 := tickLibWrapperBlocks.tickLibWrapper_block_610_taken (by simp) hz'
    (by jump_dest) rd9
  exact tickLibWrapperBlocks.tickLibWrapper_block_456 (by simp) rd10

/-- `tickToPrice(uint256)` — the `__d1` denominator is zero: `446 → 456 → REVERT`. -/
theorem t2pX_denrev {σ σ₀ A I} {g : Sat256} {t : Nat}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h36 : 36 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 2))
    (ht : t = (calldataWord I.calldata 4).toNat) (hle : t ≤ 6744)
    (hbound : ttpArg t < 0 → wExpPos (-ttpArg t) ≠ 0)
    (hdz : ttpDen (wExpVal (ttpArg t)) = 0) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachTickToPriceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_359_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_365_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_377 (by simp) (by jump_dest) rd2
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_377_stack,
    show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
        calldataWord I.calldata 4 from rfl] at rd3
  set tw := calldataWord I.calldata 4 with htw
  have hgt : UInt256.gt tw (UInt256.ofNat 6744) = ⟨0⟩ := by
    apply ugt_zero
    rw [ulit_toNat' 6744 (by decide : 6744 < UInt256.size)]
    rw [← ht]
    omega
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_476_fallthrough (by simp) hgt rd3
  have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_486 (by simp) (by jump_dest) rd4
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_486_stack] at rd5
  set warg := UInt256.mul (UInt256.ofNat 4987541511039073)
      (UInt256.sub (UInt256.ofNat 3372) tw) with hwarg
  have hsign : EVM.signed warg = ttpArg t := by
    rw [hwarg]
    exact ttpArg_signed ht hle
  have hwarg' : warg = EVM.wordOfInt (ttpArg t) := by rw [hwarg]; exact ttpArg_word ht
  -- reach pc 523 with the c0 word, via either sign branch of the wExp tail
  by_cases harg0 : ttpArg t < 0
  · have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) = ⟨0⟩ := by
      have hn : EVM.signed warg < 0 := by rw [hsign]; exact harg0
      have hge := toNat_ge_2pow255_of_signed_neg hn
      have hs0 : UInt256.slt warg ⟨0⟩ = ⟨1⟩ := by
        show UInt256.slt warg (UInt256.ofNat 0) = ⟨1⟩
        exact slt_lit_one_high (a := warg) (m := 0) (by norm_num) hge
      rw [hs0]
      exact isZero_eq_zero_of_ne (by decide)
    have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough (by simp) hslt0 rd5
    have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_600 (by simp)
      (by jump_dest) rd6
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd7
    have hneg' : UInt256.sub ⟨0⟩ warg = EVM.wordOfInt (-ttpArg t) := by
      rw [hwarg', show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, wordOfInt_sub_of]
      exact wordOfInt_cong (by
        rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
    have hslt1 : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩) ≠ ⟨0⟩ := by
      have hs : EVM.signed (UInt256.sub ⟨0⟩ warg) = -ttpArg t := by
        rw [hneg', signed_wordOfInt]
        have hb := ttpArg_bound hle
        show normalizeInt sint256T (-ttpArg t) = -ttpArg t
        exact sintNorm_of_mem _ (by omega) (by omega)
      have hnn : 0 ≤ EVM.signed (UInt256.sub ⟨0⟩ warg) := by rw [hs]; omega
      have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
      have hs0 : UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩ = ⟨0⟩ := by
        show UInt256.slt (UInt256.sub ⟨0⟩ warg) (UInt256.ofNat 0) = ⟨0⟩
        exact slt_lit_zero (a := UInt256.sub ⟨0⟩ warg) (m := 0) (by norm_num)
          (Nat.zero_le _) hlt2
      rw [hs0]
      decide
    have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hslt1
      (by jump_dest) rd7
    have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp)
      (by jump_dest) rd8
    rw [wExp636_stack, hneg', signed_wordOfInt,
        show normalizeInt sint256T (-ttpArg t) = -ttpArg t from
          sintNorm_of_mem _ (by have := ttpArg_bound hle; omega)
            (by have := ttpArg_bound hle; omega)] at rd9
    have hz : UInt256.isZero (EVM.wordOfInt (wExpPos (-ttpArg t))) = ⟨0⟩ := by
      exact isZero_eq_zero_of_ne (fun hz' =>
        hbound harg0 ((wordOfInt_wExpPos_eq_zero_iff _).mp hz'))
    have rd10 := tickLibWrapperBlocks.tickLibWrapper_block_610_fallthrough (by simp) hz rd9
    have rd11 := tickLibWrapperBlocks.tickLibWrapper_block_617 (by simp)
      (by jump_dest) rd10
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_617_stack,
      wExpVal_div_word _ harg0] at rd11
    have rd523 := tickLibWrapperBlocks.tickLibWrapper_block_523 (by simp) (by jump_dest) rd11
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_523_stack] at rd523
    have hdz' : UInt256.isZero (UInt256.ofNat 1000000000000000000 +
        EVM.wordOfInt (wExpVal (ttpArg t))) ≠ ⟨0⟩ := by
      rw [ttpDen_word,
          show EVM.wordOfInt (ttpDen (wExpVal (ttpArg t))) = ⟨0⟩ from
            (wordOfInt_uNorm_eq_zero_iff _).mpr hdz]
      decide
    have rd446 := tickLibWrapperBlocks.tickLibWrapper_block_446_taken (by simp) hdz'
      (by jump_dest) rd523
    exact tickLibWrapperBlocks.tickLibWrapper_block_456 (by simp) rd446
  · have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) ≠ ⟨0⟩ := by
      have hnn : 0 ≤ EVM.signed warg := by rw [hsign]; omega
      have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
      have hs0 : UInt256.slt warg ⟨0⟩ = ⟨0⟩ := by
        show UInt256.slt warg (UInt256.ofNat 0) = ⟨0⟩
        exact slt_lit_zero (a := warg) (m := 0) (by norm_num) (Nat.zero_le _) hlt2
      rw [hs0]
      decide
    have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken (by simp) hslt0
      (by jump_dest) rd5
    have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_636 (by simp)
      (by jump_dest) rd6
    rw [wExp636_stack, hwarg', signed_wordOfInt,
        show normalizeInt sint256T (ttpArg t) = ttpArg t from ttpArg_sintNorm hle,
        show wExpPos (ttpArg t) = wExpVal (ttpArg t) from by
          unfold wExpVal; rw [if_neg harg0]] at rd7
    have rd523 := tickLibWrapperBlocks.tickLibWrapper_block_523 (by simp) (by jump_dest) rd7
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_523_stack] at rd523
    have hdz' : UInt256.isZero (UInt256.ofNat 1000000000000000000 +
        EVM.wordOfInt (wExpVal (ttpArg t))) ≠ ⟨0⟩ := by
      rw [ttpDen_word,
          show EVM.wordOfInt (ttpDen (wExpVal (ttpArg t))) = ⟨0⟩ from
            (wordOfInt_uNorm_eq_zero_iff _).mpr hdz]
      decide
    have rd446 := tickLibWrapperBlocks.tickLibWrapper_block_446_taken (by simp) hdz'
      (by jump_dest) rd523
    exact tickLibWrapperBlocks.tickLibWrapper_block_456 (by simp) rd446

/-- Calldata too short/huge — the `size < 36` guard fails and execution reverts
    at pc 131. -/
theorem t2pX_rev {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 2)) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 32) ≠ ⟨0⟩
    rcases hshort with hs | hb
    · rw [slt_ofNat_lit_one_low (by norm_num) (by omega : I.calldata.size - 4 < 32)]
      decide
    · rw [slt_lit_one_high (a := UInt256.ofNat (I.calldata.size - 4)) (m := 32)
        (by norm_num) (by rw [ulit_toNat' _ (by omega : I.calldata.size - 4 <
          UInt256.size)]; omega)]
      decide
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachTickToPriceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_359_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_365_taken (by simp) hslt
    (by jump_dest) rd1
  exact tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd2

/-- Nonpayable calls take the `callvalue`-guard revert branch (pc 359 → 131). -/
theorem t2pX_revert_pay {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 2)) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachTickToPriceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_359_taken (by simp) hwv
    (by jump_dest) rd
  exact tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd1

/-- `tickToPrice(uint256)`: the theorem `Correct.lean` routes selector 2 to. -/
theorem tickLibWrapperTickToPriceBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = tickLibWrapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (tickLibWrapperSelBytes 2)
    rfl hsel
  have h0 : ¬ selIs I (tickLibWrapperSelBytes 0) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h1 : ¬ selIs I (tickLibWrapperSelBytes 1) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd : dispatchMsg contract I.calldata = some tickToPriceTransition :=
    tickLibWrapperDispatch_tickToPrice h0 h1 hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases h36 : 36 ≤ I.calldata.size
      · -- `36 ≤ size < 2^255 + 4`: decode succeeds, run the body.
        have hdec := t2pDecode_ok h36 hbig
        set t := (calldataWord I.calldata 4).toNat with ht
        by_cases hle : t ≤ 6744
        · by_cases hdz : ttpDen (wExpVal (ttpArg t)) = 0
          · -- zero denominator: spec `__d1` div reverts; EVM `446 → 456`.
            by_cases harg0 : ttpArg t < 0
            · by_cases hz : wExpPos (-ttpArg t) = 0
              · have hbody : ExecTransitionBody config contract
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                    tickToPriceTransition.body .reverted :=
                  t2pTransitionReverts_call
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I) t
                    ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                    (by simp only [initState]; exact hwv)
                    (by simp only [initState]; exact hbig)
                    (t2pBodyStele_divZero config
                      { contract := contract,
                        locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)),
                        immutables := ∅ }
                      _ t hle rfl (store_get_self _ _ _) harg0 hz)
                    (store_get_self _ _ _)
                exact (t2pX_divrev (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig
                    h36 hsel ht hle harg0 hz)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · have hbody : ExecTransitionBody config contract
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                    tickToPriceTransition.body .reverted :=
                  t2pTransitionReverts_call
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I) t
                    ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                    (by simp only [initState]; exact hwv)
                    (by simp only [initState]; exact hbig)
                    (t2pBodyStele_denZero config
                      { contract := contract,
                        locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)),
                        immutables := ∅ }
                      _ t hle rfl (store_get_self _ _ _) (fun _ => hz) hdz)
                    (store_get_self _ _ _)
                exact (t2pX_denrev (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig
                    h36 hsel ht hle (fun _ => hz) hdz)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hbody : ExecTransitionBody config contract
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                  tickToPriceTransition.body .reverted :=
                t2pTransitionReverts_call
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I) t
                  ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                  (by simp only [initState]; exact hwv)
                  (by simp only [initState]; exact hbig)
                  (t2pBodyStele_denZero config
                    { contract := contract,
                      locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)),
                      immutables := ∅ }
                    _ t hle rfl (store_get_self _ _ _) (fun hn => absurd hn harg0) hdz)
                  (store_get_self _ _ _)
              exact (t2pX_denrev (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig
                  h36 hsel ht hle (fun hn => absurd hn harg0) hdz)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · by_cases harg0 : ttpArg t < 0
            · by_cases hz : wExpPos (-ttpArg t) = 0
              · -- `1e36 / 0` inside `wExp_body`: spec reverts; EVM `610 → 456`.
                have hbody : ExecTransitionBody config contract
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                    tickToPriceTransition.body .reverted :=
                  t2pTransitionReverts_call
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I) t
                    ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                    (by simp only [initState]; exact hwv)
                    (by simp only [initState]; exact hbig)
                    (t2pBodyStele_divZero config
                      { contract := contract,
                        locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)),
                        immutables := ∅ }
                      _ t hle rfl (store_get_self _ _ _) harg0 hz)
                    (store_get_self _ _ _)
                exact (t2pX_divrev (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig
                    h36 hsel ht hle harg0 hz)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · -- ordinary success.
                obtain ⟨cs, hb⟩ := t2pTransitionReturns
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I) t
                  ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                  (by simp only [initState]; exact hwv)
                  (by simp only [initState]; exact hbig)
                  hle (fun hn => hz) hdz
                  (store_get_self ∅ "tick" (.int (Int.ofNat t)))
                exact (t2pX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig
                    h36 hsel ht hle (fun hn => hz) hdz)
                  |>.reEquivExecution hcode hd hdec hb
                    (returnEquiv_of_encode (by
                      have henc := uint256ReturnEncoding (EVM.wordOfInt (ttpResult t))
                      rw [ttpResult_toNat t] at henc
                      exact henc))
            · -- `ttpArg t ≥ 0`: positive path.
              obtain ⟨cs, hb⟩ := t2pTransitionReturns
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) t
                ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
                (by simp only [initState]; exact hwv)
                (by simp only [initState]; exact hbig)
                hle (fun hn => absurd hn harg0) hdz
                (store_get_self ∅ "tick" (.int (Int.ofNat t)))
              exact (t2pX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig
                  h36 hsel ht hle (fun hn => absurd hn harg0) hdz)
                |>.reEquivExecution hcode hd hdec hb
                  (returnEquiv_of_encode (by
                    have henc := uint256ReturnEncoding (EVM.wordOfInt (ttpResult t))
                    rw [ttpResult_toNat t] at henc
                    exact henc))
        · -- `tick > 6744`: spec `require` reverts; EVM `476 → 576`.
          have hbody : ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
              tickToPriceTransition.body .reverted :=
            t2pTransitionReverts_call
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) t
              ((∅ : Store).insert "tick" (.int (Int.ofNat t)))
              (by simp only [initState]; exact hwv)
              (by simp only [initState]; exact hbig)
              (t2pBodyStele_req config
                { contract := contract,
                  locals := (∅ : Store).insert "tick" (.int (Int.ofNat t)),
                  immutables := ∅ }
                _ t hle (store_get_self _ _ _))
              (store_get_self _ _ _)
          have hgt' : 6744 < (calldataWord I.calldata 4).toNat := by
            rw [← ht]; omega
          exact (t2pX_rev_gate (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig
              h36 hsel hgt')
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · -- `4 ≤ size < 36`: decode fails (not enough args bytes) → revert at 131.
        have hdec : config.externalABI.decodeCalldata?
            (tickToPriceTransition.params.map Param.name)
            (transitionSignature tickToPriceTransition).paramTypes I.calldata = none :=
          t2pDecode_none hsz (Or.inl (by omega))
        have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
          t2pX_rev hcode hwv hsz hsize (Or.inl (by omega)) hsel
        rcases hrd with hOOG | ⟨g', o, hrev⟩
        · rw [← hcode] at hOOG
          exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
            simpa [Sat256.ofUInt256_toNat] using hOOG))
        · rw [← hcode] at hrev
          exact reEquiv_decodingFailed hd hdec (Xi_revert_of_X (g := g) (by
            simpa [Sat256.ofUInt256_toNat] using hrev))
    · -- `size ≥ 2^255 + 4`: decode fails (huge args) → revert at 131.
      have hdec : config.externalABI.decodeCalldata?
          (tickToPriceTransition.params.map Param.name)
          (transitionSignature tickToPriceTransition).paramTypes I.calldata = none :=
        t2pDecode_none hsz (Or.inr (by omega))
      have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
        t2pX_rev hcode hwv hsz hsize (Or.inr (by omega)) hsel
      rcases hrd with hOOG | ⟨g', o, hrev⟩
      · rw [← hcode] at hOOG
        exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
          simpa [Sat256.ofUInt256_toNat] using hOOG))
      · rw [← hcode] at hrev
        exact reEquiv_decodingFailed hd hdec (Xi_revert_of_X (g := g) (by
          simpa [Sat256.ofUInt256_toNat] using hrev))
  · -- nonpayable: revert at 131 on both sides.
    have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
      t2pX_revert_pay hcode hwv hsz hsize hsel
    rcases hrd with hOOG | ⟨g', o, hrev⟩
    · rw [← hcode] at hOOG
      exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
        simpa [Sat256.ofUInt256_toNat] using hOOG))
    · rw [← hcode] at hrev
      have hΞ : Ξ σ σ₀ g A I = .ok (.revert g' o) :=
        Xi_revert_of_X (g := g) (by simpa [Sat256.ofUInt256_toNat] using hrev)
      by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases h36 : 36 ≤ I.calldata.size
        · have hdec := t2pDecode_ok h36 hbig
          have hbody : ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              ((∅ : Store).insert "tick"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
              tickToPriceTransition.body .reverted := by
            rw [tickToPriceBody_eq]
            exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)
          exact reEquiv_execution hd hdec hbody (execResultsEquiv.revert hΞ rfl)
        · have hdec : config.externalABI.decodeCalldata?
              (tickToPriceTransition.params.map Param.name)
              (transitionSignature tickToPriceTransition).paramTypes I.calldata = none :=
            t2pDecode_none hsz (Or.inl (by omega))
          exact reEquiv_decodingFailed hd hdec hΞ
      · have hdec : config.externalABI.decodeCalldata?
            (tickToPriceTransition.params.map Param.name)
            (transitionSignature tickToPriceTransition).paramTypes I.calldata = none :=
          t2pDecode_none hsz (Or.inr (by omega))
        exact reEquiv_decodingFailed hd hdec hΞ

end Benchmarks.Midnight.TickLibWrapper
