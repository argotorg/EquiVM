import Examples.BlindAuction.Reveal.PlaceBid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000
namespace BlindAuction

-- LIBRARY CANDIDATE: `Reasoning.Reach`.
-- Variant-indexed loop rule carrying stack, memory/active words, and account state.
theorem scratch_RD_whileLoopCarryAcc {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {rdata : ByteArray} {α : Type}
    (header exit : UInt256) (Inv : ℕ → α → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256)
    (hexit : ∀ a, Inv 0 a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
        ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) rdata (acc a) k' C')
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
        ∃ a' k' C',
          Inv v a' ∧
            RD code ee g s0 header (stk a') (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a, Inv v a → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ a' k' C',
        Inv 0 a' ∧ RD code ee g s0 exit (exitStk a') (mem a') (aw a') rdata (acc a') k' C' := by
  exact Reasoning.Reach.RD.whileLoopCarryFull header exit Inv stk mem aw acc exitStk hexit hbody

-- LIBRARY CANDIDATE: `Reasoning.SolmBody`.
-- Variant-indexed for-loop rule that carries both locals and EVM state.
theorem scratch_execFor_varEVM {cfg : Config} {C : ContractDecl}
    {condExpr : Expr} {post body : List Stmt}
    (P : ℕ → Solm.Store → EVM.State → Prop)
    (hfalse : ∀ L evm, P 0 L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool false))
    (htrue : ∀ v L evm, P (v + 1) L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool true))
    (hstep : ∀ v L evm, P (v + 1) L evm →
        ∃ L1 evm1, ExecBlock cfg { contract := C, locals := L } evm body
              (.ok { contract := C, locals := L1 } evm1) ∧
            ∃ L2 evm2, ExecBlock cfg { contract := C, locals := L1 } evm1 post
              (.ok { contract := C, locals := L2 } evm2) ∧ P v L2 evm2) :
    ∀ v L evm, P v L evm → ∃ L' evm',
      ExecForLoop cfg { contract := C, locals := L } evm condExpr post body
        (.ok { contract := C, locals := L' } evm') ∧ P 0 L' evm' := by
  exact Reasoning.Theory.execFor_var_state_continue P hfalse htrue
    (fun v L evm hP => by
      obtain ⟨L1, evm1, hbody, L2, evm2, hpost, hP1⟩ := hstep v L evm hP
      exact ⟨L1, evm1, Or.inl hbody, L2, evm2, hpost, hP1⟩)


theorem scratch_blindAuctionRevealX_loop_from_body {I} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel : UInt256)
    (Inv : ℕ → α → Prop) (idx refund : α → UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (hvariant : ∀ v a, Inv v a → (idx a).toNat + v = len.toNat ∧
      (idx a).toNat ≤ len.toNat)
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
        RD blindAuctionBytecode I g s0 ⟨1023⟩
          (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a) (aw a) rdata (acc a) k C →
        ∃ a' k' C',
          Inv v a' ∧
          RD blindAuctionBytecode I g s0 ⟨1014⟩
            (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
              secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
            (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a, Inv v a → ∀ k C,
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        (mem a) (aw a) rdata (acc a) k C →
      ∃ a' k' C',
        Inv 0 a' ∧
        RD blindAuctionBytecode I g s0 ⟨1331⟩
          (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a') (aw a') rdata (acc a') k' C' := by
  refine scratch_RD_whileLoopCarryAcc (code := blindAuctionBytecode) (ee := I) (g := g)
    (s0 := s0) (rdata := rdata) (header := ⟨1014⟩) (exit := ⟨1331⟩)
    (Inv := Inv)
    (stk := fun a =>
      scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
    (mem := mem) (aw := aw) (acc := acc)
    (exitStk := fun a =>
      scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel) ?_ ?_
  · intro a hInv k C rd
    rcases hvariant 0 a hInv with ⟨hvar, _hle⟩
    exact scratch_blindAuctionRevealX_loopCond_exit rd (by omega)
  · intro v a hInv k C rd
    rcases hvariant (v + 1) a hInv with ⟨hvar, _hle⟩
    obtain ⟨k1, C1, rd1023⟩ := blindAuctionRevealX_loopCond_taken
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem a) (aw := aw a) (rdata := rdata) (acc := acc a)
      (i := idx a) (refund := refund a) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (by simpa [scratch_revealEvmLoopStack] using rd)
      (by omega)
    exact hbody v a hInv k1 C1 (by simpa [scratch_revealEvmLoopStack] using rd1023)


def scratch_revealLengthStore (callargs : Store) (len : UInt256) : Store :=
  callargs.insert "length" (.int (Int.ofNat len.toNat))

def scratch_revealRefundStore (callargs : Store) (len refund : UInt256) : Store :=
  (scratch_revealLengthStore callargs len).insert "refund" (.int (Int.ofNat refund.toNat))

def scratch_revealLoopStore (callargs : Store) (len refund i : UInt256) : Store :=
  (scratch_revealRefundStore callargs len refund).insert "i" (.int (Int.ofNat i.toNat))

def scratch_revealCallStore (callargs : Store) (len refund i : UInt256)
    (success : Bool) (out : ByteArray) : Store :=
  (scratch_revealLoopStore callargs len refund i).insert "success" (.bool success)
    |>.insert "_data" (.bytes out)

def scratch_revealCallStoreOf (locals : Store) (success : Bool) (out : ByteArray) : Store :=
  locals.insert "success" (.bool success) |>.insert "_data" (.bytes out)

theorem scratch_revealCallStore_success_get (callargs : Store) (len refund i : UInt256)
    (success : Bool) (out : ByteArray) :
    (scratch_revealCallStore callargs len refund i success out).get? "success" =
      some (.bool success) := by
  unfold scratch_revealCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem scratch_evalExpr_reveal_success (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256) (success : Bool) (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealCallStore callargs len refund i success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((scratch_revealCallStore callargs len refund i success out).get? "success") =
      .ok (.bool success)
  rw [scratch_revealCallStore_success_get]
  rfl

theorem scratch_revealCallStoreOf_success_get (locals : Store) (success : Bool)
    (out : ByteArray) :
    (scratch_revealCallStoreOf locals success out).get? "success" =
      some (.bool success) := by
  unfold scratch_revealCallStoreOf
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem scratch_evalExpr_reveal_success_of (evm : EVM.State) (locals : Store)
    (success : Bool) (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealCallStoreOf locals success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((scratch_revealCallStoreOf locals success out).get? "success") =
      .ok (.bool success)
  rw [scratch_revealCallStoreOf_success_get]
  rfl

def scratch_revealLoopPostStmts : List Stmt :=
  [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]

def scratch_revealLoopBodyStmts : List Stmt :=
  [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
    .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
    .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
    .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
    .ite
      (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
        (.keccak256 (.abiEncodePacked
          [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
      [.continue] [],
    .assign .localVar { base := "refund" }
      (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
    .ite
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
      [ .internalCall "placeBid" [sender, .var "value"] "ok",
        .ite (.var "ok")
          [ .assign .localVar { base := "refund" }
              (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
    .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]

def scratch_revealForStmt : Stmt :=
  .for [ .letDecl "i" (some uint256) (.intLit 0) ]
    (.binary .lt (.var "i") (.var "length"))
    scratch_revealLoopPostStmts
    scratch_revealLoopBodyStmts

theorem scratch_revealLoopStore_length_get (callargs : Store) (len refund i : UInt256) :
    (scratch_revealLoopStore callargs len refund i).get? "length" =
      some (.int (Int.ofNat len.toNat)) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide

theorem scratch_revealLoopStore_refund_get (callargs : Store) (len refund i : UInt256) :
    (scratch_revealLoopStore callargs len refund i).get? "refund" =
      some (.int (Int.ofNat refund.toNat)) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore
  rw [store_get_ne, store_get_self]
  decide

theorem scratch_revealLoopStore_i_get (callargs : Store) (len refund i : UInt256) :
    (scratch_revealLoopStore callargs len refund i).get? "i" =
      some (.int (Int.ofNat i.toNat)) := by
  unfold scratch_revealLoopStore
  rw [store_get_self]

theorem scratch_revealLoopStore_values_get {callargs : Store} {values : List Value}
    {len refund i : UInt256}
    (hvalues : callargs.get? "values" = some (.array values)) :
    (scratch_revealLoopStore callargs len refund i).get? "values" = some (.array values) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hvalues
  · decide
  · decide
  · decide

theorem scratch_revealLoopStore_fakes_get {callargs : Store} {fakes : List Value}
    {len refund i : UInt256}
    (hfakes : callargs.get? "fakes" = some (.array fakes)) :
    (scratch_revealLoopStore callargs len refund i).get? "fakes" = some (.array fakes) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hfakes
  · decide
  · decide
  · decide

theorem scratch_revealLoopStore_secrets_get {callargs : Store} {secrets : List Value}
    {len refund i : UInt256}
    (hsecrets : callargs.get? "secrets" = some (.array secrets)) :
    (scratch_revealLoopStore callargs len refund i).get? "secrets" = some (.array secrets) := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hsecrets
  · decide
  · decide
  · decide

theorem scratch_revealLoopStore_bids_none {callargs : Store} {len refund i : UInt256}
    (hbids : callargs.get? "bids" = none) :
    (scratch_revealLoopStore callargs len refund i).get? "bids" = none := by
  unfold scratch_revealLoopStore scratch_revealRefundStore scratch_revealLengthStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact hbids
  · decide
  · decide
  · decide

theorem scratch_evalExpr_reveal_loop_cond_true (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256) (hbound : i.toNat < len.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (.binary .lt (.var "i") (.var "length")) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "i"
      (Int.ofNat i.toNat) (scratch_revealLoopStore_i_get callargs len refund i),
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "length"
      (Int.ofNat len.toNat) (scratch_revealLoopStore_length_get callargs len refund i),
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_loop_cond_false (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256) (hbound : len.toNat ≤ i.toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "i"
      (Int.ofNat i.toNat) (scratch_revealLoopStore_i_get callargs len refund i),
    evalExpr_reveal_var_int evm (scratch_revealLoopStore callargs len refund i) "length"
      (Int.ofNat len.toNat) (scratch_revealLoopStore_length_get callargs len refund i),
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_loop_cond_true_of_get (evm : EVM.State) (locals : Store)
    (len i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (hbound : i.toNat < len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt (.var "i") (.var "length")) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_loop_cond_false_of_get (evm : EVM.State) (locals : Store)
    (len i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (hbound : len.toNat ≤ i.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [
    evalExpr_reveal_var_int evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound

theorem scratch_evalExpr_reveal_local_array_index_norm (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (idx : UInt256) (rawv v : Value)
    (harr : locals.get? name = some (.array xs))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < xs.length)
    (hlookup : lookupNth? xs idx.toNat = some rawv)
    (hnorm : normalizeRawBoolWord? rawv = .ok v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.index (.var name) (.var "i")) = .ok v := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_value evm locals name (.array xs) harr,
    evalExpr_reveal_var_value evm locals "i" (.int (Int.ofNat idx.toNat)) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  simp only
  rw [if_pos]
  · simp [hlookup, hnorm]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · simpa using hbound

theorem scratch_evalExpr_reveal_local_array_index_revert (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (idx : UInt256) (rawv : Value)
    (harr : locals.get? name = some (.array xs))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < xs.length)
    (hlookup : lookupNth? xs idx.toNat = some rawv)
    (hnorm : normalizeRawBoolWord? rawv = .revert) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.index (.var name) (.var "i")) = .revert := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_value evm locals name (.array xs) harr,
    evalExpr_reveal_var_value evm locals "i" (.int (Int.ofNat idx.toNat)) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  simp only
  rw [if_pos]
  · simp [hlookup, hnorm]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · simpa using hbound

def scratch_revealBidEvaledRef (evm : EVM.State) (i : UInt256) : EvaledStorageRef :=
  { base := "bids",
    steps := [.mindex (.address evm.executionEnv.source),
      .aindex (.int (Int.ofNat i.toNat))] }

def scratch_revealBidToCheckStore (callargs : Store) (evm : EVM.State)
    (len refund i : UInt256) : Store :=
  (scratch_revealLoopStore callargs len refund i).insert "bidToCheck"
    (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)

def scratch_revealValueStore (callargs : Store) (evm : EVM.State)
    (len refund i value : UInt256) : Store :=
  (scratch_revealBidToCheckStore callargs evm len refund i).insert "value"
    (.int (Int.ofNat value.toNat))

def scratch_revealFakeStore (callargs : Store) (evm : EVM.State)
    (len refund i value : UInt256) (fake : Bool) : Store :=
  (scratch_revealValueStore callargs evm len refund i value).insert "fake" (.bool fake)

def scratch_revealSecretStore (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) : Store :=
  (scratch_revealFakeStore callargs evm len refund i value fake).insert "secret"
    (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))

def scratch_revealRefundAddedStore (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) : Store :=
  (scratch_revealSecretStore callargs evm len refund i value secret fake).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat)))

def scratch_revealRefundPlacedStore (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) : Store :=
  ((scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false).insert
      "ok" (.bool true)).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat - value.toNat)))

def scratch_revealBidFieldRef (evm : EVM.State) (i : UInt256) (field : Ident) :
    EvaledStorageRef :=
  { scratch_revealBidEvaledRef evm i with
    steps := (scratch_revealBidEvaledRef evm i).steps ++ [.field field] }

def scratch_revealBidBlindedSlot (evm : EVM.State) (i : UInt256) : UInt256 :=
  bidsElemSlot (.address evm.executionEnv.source) (.int (Int.ofNat i.toNat))

def scratch_revealBidDepositSlot (evm : EVM.State) (i : UInt256) : UInt256 :=
  scratch_revealBidBlindedSlot evm i + ⟨1⟩

theorem scratch_revealBid_arrayIndexInBounds_ok (evm : EVM.State) (i len : UInt256)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
      [.mindex (.address evm.executionEnv.source)] (.int (Int.ofNat i.toNat)) = .ok () := by
  simp [arrayIndexInBounds?, storageTypeAt?, storageTypeStep?, blindAuctionConfig,
    blindAuctionStorageLayout, blindAuctionContract, storageDecls, bidStructTy, uint256St,
    bytes32St, blindAuctionStorageLocLoad_uint256, hlen, hbound]

theorem scratch_evalStorageRef_reveal_bid_ok (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i) := by
  have hbounds := scratch_revealBid_arrayIndexInBounds_ok evm i len hlen hbound
  simp only [bidElemRef, sender, evalStorageRef, evalStorageRefSteps.eq_def,
    evalStorageRefStep.eq_def, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, List.nil_append, scratch_revealBidEvaledRef,
    scratch_revealLoopStore_i_get]
  rw [hbounds]

theorem scratch_revealBid_storageType (evm : EVM.State) (i : UInt256) :
    storageTypeAt? blindAuctionContract.storage (scratch_revealBidEvaledRef evm i) =
      some bidStructTy := by
  simp [scratch_revealBidEvaledRef, storageTypeAt?, storageTypeStep?, blindAuctionContract,
    storageDecls, bidStructTy]

theorem scratch_resolveStorageRef_reveal_bid_ok (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256)
    (hbids : callargs.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    resolveStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i, bidStructTy) := by
  exact resolveStorageRef?_ok
    (scratch_revealLoopStore_bids_none (len := len) (refund := refund) (i := i) hbids)
    (scratch_evalStorageRef_reveal_bid_ok evm callargs len refund i hlen hbound)
    (scratch_revealBid_storageType evm i)

theorem scratch_letStorage_reveal_bidToCheck (evm : EVM.State) (callargs : Store)
    (len refund i : UInt256)
    (hbids : callargs.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    ExecStmt blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm (.letStorage "bidToCheck" (bidElemRef sender (.var "i")))
      (.ok
        { contract := blindAuctionContract,
          locals := (scratch_revealLoopStore callargs len refund i).insert "bidToCheck"
            (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) }
        evm) := by
  exact ExecStmt.letStorage
    (scratch_resolveStorageRef_reveal_bid_ok evm callargs len refund i hbids hlen hbound)

theorem scratch_revealBidToCheckStore_bid_get (callargs : Store) (evm : EVM.State)
    (len refund i : UInt256) :
    (scratch_revealBidToCheckStore callargs evm len refund i).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealBidToCheckStore
  rw [store_get_self]

theorem scratch_revealSecretStore_bid_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore scratch_revealValueStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · exact scratch_revealBidToCheckStore_bid_get callargs evm len refund i
  · decide
  · decide
  · decide

theorem scratch_revealSecretStore_value_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "value" =
      some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore scratch_revealValueStore
  rw [store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide

theorem scratch_revealSecretStore_fake_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "fake" =
      some (.bool fake) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore
  rw [store_get_ne, store_get_self]
  decide

theorem scratch_revealSecretStore_refund_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStore callargs evm len refund i value secret fake).get? "refund" =
      some (.int (Int.ofNat refund.toNat)) := by
  unfold scratch_revealSecretStore scratch_revealFakeStore scratch_revealValueStore
  rw [store_get_ne, store_get_ne, store_get_ne]
  · unfold scratch_revealBidToCheckStore
    rw [store_get_ne]
    · exact scratch_revealLoopStore_refund_get callargs len refund i
    · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStore_bid_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_ne]
  · exact scratch_revealSecretStore_bid_get callargs evm len refund i value secret fake
  · decide

theorem scratch_revealRefundAddedStore_value_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "value" = some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_ne]
  · exact scratch_revealSecretStore_value_get callargs evm len refund i value secret fake
  · decide

theorem scratch_revealRefundAddedStore_fake_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "fake" = some (.bool fake) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_ne]
  · exact scratch_revealSecretStore_fake_get callargs evm len refund i value secret fake
  · decide

theorem scratch_revealRefundAddedStore_refund_get (callargs : Store) (evm : EVM.State)
    (len refund i value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake).get?
      "refund" = some (.int (Int.ofNat (refund.toNat + deposit.toNat))) := by
  unfold scratch_revealRefundAddedStore
  rw [store_get_self]

theorem scratch_resolveStorageRef_reveal_bid_blinded_ok (evm : EVM.State)
    (locals : Store) (i : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)) :
    resolveStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals }
      evm (aliasF "bidToCheck" "blindedBid") =
        .ok (scratch_revealBidFieldRef evm i "blindedBid", bytes32St) := by
  have hbid' :
      locals["bidToCheck"]? =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [← Std.HashMap.get?_eq_getElem?] using hbid
  simp [resolveStorageRef?, aliasF, evalStorageRefFrom?, evalStorageRefStep,
    EvalResult.ofOption, EvalResult.bind, bind, pure,
    hbid',
    scratch_revealBidEvaledRef, scratch_revealBidFieldRef, storageTypeStep?, bidStructTy,
    bytes32St]

theorem scratch_resolveStorageRef_reveal_bid_deposit_ok (evm : EVM.State)
    (locals : Store) (i : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)) :
    resolveStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals }
      evm (aliasF "bidToCheck" "deposit") =
        .ok (scratch_revealBidFieldRef evm i "deposit", uint256St) := by
  have hbid' :
      locals["bidToCheck"]? =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [← Std.HashMap.get?_eq_getElem?] using hbid
  simp [resolveStorageRef?, aliasF, evalStorageRefFrom?, evalStorageRefStep,
    EvalResult.ofOption, EvalResult.bind, bind, pure,
    hbid',
    scratch_revealBidEvaledRef, scratch_revealBidFieldRef, storageTypeStep?, bidStructTy,
    uint256St]

theorem scratch_revealBid_blinded_layout (evm : EVM.State) (i : UInt256) :
    blindAuctionConfig.storage.layout (scratch_revealBidFieldRef evm i "blindedBid") =
      fun _ => some (blindAuctionBytes32Loc (scratch_revealBidBlindedSlot evm i)) := by
  funext evm'
  simp [scratch_revealBidFieldRef, scratch_revealBidEvaledRef, scratch_revealBidBlindedSlot]

theorem scratch_revealBid_deposit_layout (evm : EVM.State) (i : UInt256) :
    blindAuctionConfig.storage.layout (scratch_revealBidFieldRef evm i "deposit") =
      fun _ => some (blindAuctionUint256Loc (scratch_revealBidDepositSlot evm i)) := by
  funext evm'
  simp [scratch_revealBidFieldRef, scratch_revealBidEvaledRef, scratch_revealBidDepositSlot,
    scratch_revealBidBlindedSlot]

theorem scratch_evalExpr_reveal_bid_blinded (evm : EVM.State) (locals : Store)
    (i blinded : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage (aliasF "bidToCheck" "blindedBid")) =
        .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE blinded)) := by
  rw [evalExpr?]
  simp only [scratch_resolveStorageRef_reveal_bid_blinded_ok evm locals i hbid,
    EvalResult.bind, bind]
  unfold bytes32St
  rw [readStorage?_elem (cfg := blindAuctionConfig)
    (evm := evm) (er := scratch_revealBidFieldRef evm i "blindedBid")
    (t := .bytes ⟨31, by decide⟩)
    (loc := blindAuctionBytes32Loc (scratch_revealBidBlindedSlot evm i))
    (scratch_revealBid_blinded_layout evm i)]
  rw [blindAuctionStorageLocLoad_bytes32, hblinded]

theorem scratch_evalExpr_reveal_hash_guard_true (evm : EVM.State) (locals : Store)
    (i blinded : UInt256) (hashBytes : List UInt8)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (hne : EVM.Word.toBytesBE blinded ≠ hashBytes) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
        scratch_revealPackedHashExpr) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [scratch_evalExpr_reveal_bid_blinded evm locals i blinded hbid hblinded,
    hhash, EvalResult.bind, bind]
  simp [evalBinaryOp?, hne]

theorem scratch_evalExpr_reveal_hash_guard_false (evm : EVM.State) (locals : Store)
    (i blinded : UInt256) (hashBytes : List UInt8)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
        scratch_revealPackedHashExpr) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [scratch_evalExpr_reveal_bid_blinded evm locals i blinded hbid hblinded,
    hhash, EvalResult.bind, bind]
  subst hashBytes
  simp [evalBinaryOp?]

theorem scratch_revealLoopBody_continue_hash_mismatch (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (hne : EVM.Word.toBytesBE blinded ≠ hashBytes) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.continue
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake }
        evm) := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck evm callargs len refund i hbids hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStore callargs evm len refund i
  let L2 := scratch_revealValueStore callargs evm len refund i value
  let L3 := scratch_revealFakeStore callargs evm len refund i value fake
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
    [ .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
      .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_values_get (len := len) (refund := refund) (i := i) hvalues)
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
    [ .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_fakes_get (len := len) (refund := refund) (i := i) hfakes)
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
    [ .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using
        (scratch_revealLoopStore_secrets_get (len := len) (refund := refund) (i := i)
          hsecrets)
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using (scratch_revealLoopStore_i_get callargs len refund i)
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
    [ .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    dsimp [L4, scratch_revealSecretStore, scratch_revealFakeStore, scratch_revealValueStore]
    change
      ((((scratch_revealBidToCheckStore callargs evm len refund i).insert "value"
              (.int (Int.ofNat value.toNat))).insert "fake" (.bool fake)).insert "secret"
          (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))).get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)
    rw [store_get_ne, store_get_ne, store_get_ne]
    · exact scratch_revealBidToCheckStore_bid_get callargs evm len refund i
    · decide
    · decide
    · decide
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool true) := by
    simpa [scratch_revealPackedHashExpr] using
      scratch_evalExpr_reveal_hash_guard_true evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) hne
  refine ExecBlock.consContinue ?_
  refine ExecStmt.iteTrue hguard ?_
  exact ExecBlock.consContinue ExecStmt.continue

theorem scratch_revealLoopBody_prefix_exec (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret : UInt256)
    (fake : Bool) (fakeRaw : Value) {result : ExecResult}
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake }
        evm (List.drop 4 scratch_revealLoopBodyStmts) result) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts result := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck evm callargs len refund i hbids hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStore callargs evm len refund i
  let L2 := scratch_revealValueStore callargs evm len refund i value
  let L3 := scratch_revealFakeStore callargs evm len refund i value fake
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_values_get (len := len) (refund := refund) (i := i) hvalues)
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_fakes_get (len := len) (refund := refund) (i := i) hfakes)
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using
        (scratch_revealLoopStore_secrets_get (len := len) (refund := refund) (i := i)
          hsecrets)
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using (scratch_revealLoopStore_i_get callargs len refund i)
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  simpa [L4, scratch_revealLoopBodyStmts] using htail

/-
theorem scratch_revealLoopBody_prefix (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret : UInt256)
    (fake : Bool) (fakeRaw : Value)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))) :
    ABlock blindAuctionConfig evm
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      scratch_revealLoopBodyStmts
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStore callargs evm len refund i value secret fake }
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ] := by
  refine ⟨fun htail => ?_⟩
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck evm callargs len refund i hbids hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStore callargs evm len refund i
  let L2 := scratch_revealValueStore callargs evm len refund i value
  let L3 := scratch_revealFakeStore callargs evm len refund i value fake
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
    [ .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
      .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm) at htail
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
    [ .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
      .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (ExecResult.continue { contract := blindAuctionContract, locals := L4 } evm) at htail
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_values_get (len := len) (refund := refund) (i := i) hvalues)
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
    [ .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
      .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_fakes_get (len := len) (refund := refund) (i := i) hfakes)
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStore, L1, scratch_revealBidToCheckStore,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using
      (scratch_revealLoopStore_i_get callargs len refund i)
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  change ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
    [ .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
      .ite
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
        [.continue] [],
      .assign .localVar { base := "refund" }
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
      .ite
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
      .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
    (.continue { contract := blindAuctionContract, locals := L4 } evm)
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using
        (scratch_revealLoopStore_secrets_get (len := len) (refund := refund) (i := i)
          hsecrets)
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStore, scratch_revealValueStore, L1,
      scratch_revealBidToCheckStore, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      using (scratch_revealLoopStore_i_get callargs len refund i)
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  simpa [L4] using htail
-/

theorem scratch_evalExpr_reveal_bid_deposit (evm : EVM.State) (locals : Store)
    (i deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage (aliasF "bidToCheck" "deposit")) =
        .ok (.int (Int.ofNat deposit.toNat)) := by
  rw [evalExpr?]
  simp only [scratch_resolveStorageRef_reveal_bid_deposit_ok evm locals i hbid,
    EvalResult.bind, bind]
  unfold uint256St
  rw [readStorage?_elem (cfg := blindAuctionConfig)
    (evm := evm) (er := scratch_revealBidFieldRef evm i "deposit")
    (t := .int uint256Int)
    (loc := blindAuctionUint256Loc (scratch_revealBidDepositSlot evm i))
    (scratch_revealBid_deposit_layout evm i)]
  rw [blindAuctionStorageLocLoad_uint256, hdeposit]

theorem scratch_evalExpr_reveal_placeBid_cond_true (evm : EVM.State) (locals : Store)
    (i value deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hfake : locals.get? "fake" = some (.bool false))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hle : value.toNat ≤ deposit.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr?, evalExpr_reveal_var_value evm locals "fake" (.bool false) hfake,
    EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption, pure,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue]
  simp [evalBinaryOp?]
  exact hle

theorem scratch_evalExpr_reveal_placeBid_cond_false_fake (evm : EVM.State) (locals : Store)
    (i value deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hfake : locals.get? "fake" = some (.bool true))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
        .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr?, evalExpr_reveal_var_value evm locals "fake" (.bool true) hfake,
    EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption, pure,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue]
  simp [evalBinaryOp?]

theorem scratch_evalExpr_reveal_placeBid_cond_false_deposit (evm : EVM.State) (locals : Store)
    (i value deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hfake : locals.get? "fake" = some (.bool false))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hlt : deposit.toNat < value.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .and (.unary .not (.var "fake"))
        (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
        .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr?, evalExpr_reveal_var_value evm locals "fake" (.bool false) hfake,
    EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption, pure,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue]
  simp [evalBinaryOp?]
  omega

theorem scratch_blindAuctionStorageLocStore_bytes32 (evm : EVM.State)
    (slot word : UInt256) (v : Value)
    (hval : valueToWord v = some word) :
    storageLocStore evm (blindAuctionBytes32Loc slot) v =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word) := by
  simpa [blindAuctionBytes32Loc, Reasoning.Theory.bytes32Loc] using
    storageLocStore_bytes32 evm slot word v hval

def scratch_revealZeroBlindedState (evm : EVM.State) (i : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (scratch_revealBidBlindedSlot evm i) (EVM.Word.ofNat 0)

theorem scratch_revealBidEvaledRef_storageStore (evm : EVM.State)
    (a : EVM.Address) (slot word i : UInt256) :
    scratch_revealBidEvaledRef (Solm.EVM.storageStore evm a slot word) i =
      scratch_revealBidEvaledRef evm i := by
  unfold scratch_revealBidEvaledRef Solm.EVM.storageStore
  cases h : evm.lookupAccount a <;> simp [Option.option, h, Ethereum.State.setAccount]

theorem scratch_evalExpr_reveal_cast_zero_bytes32 (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.cast (.intLit 0) bytes32St) =
        .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) := by
  rw [evalExpr?]
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  unfold bytes32St castValue? EvalResult.ofOption
  simp [EVM.Word.ofNat]

theorem scratch_assign_reveal_blinded_zero (evm : EVM.State) (locals : Store)
    (i : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)) :
    assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      .storage (aliasF "bidToCheck" "blindedBid")
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
        .ok ({ contract := blindAuctionContract, locals := locals },
          scratch_revealZeroBlindedState evm i) := by
  rw [assignStorageRef?]
  simp only [scratch_resolveStorageRef_reveal_bid_blinded_ok evm locals i hbid,
    EvalResult.bind, bind]
  have hloc := scratch_revealBid_blinded_layout evm i
  simp only [hloc, EvalResult.ofOption, Option.bind]
  rw [scratch_blindAuctionStorageLocStore_bytes32 (word := EVM.Word.ofNat 0)]
  · rfl
  · native_decide

theorem scratch_assign_local_value (evm : EVM.State) (locals : Store)
    (name : Ident) (old value : Value)
    (hget : locals.get? name = some old) :
    assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      .localVar { base := name } value =
        .ok ({ contract := blindAuctionContract, locals := locals.insert name value }, evm) := by
  have hget' : locals[name]? = some old := by
    simpa [← Std.HashMap.get?_eq_getElem?] using hget
  simp [assignStorageRef?, updateLocalPath?, hget', EvalResult.bind, bind, pure]

theorem scratch_evalExprs_reveal_placeBid_args (evm : EVM.State) (locals : Store)
    (value : UInt256)
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat))) :
    evalExprs? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      [sender, .var "value"] =
        .ok [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)] := by
  simp [evalExprs?, evalExpr_reveal_sender evm locals,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue,
    EvalResult.bind, bind, pure]

theorem scratch_evalExpr_reveal_refund_add_deposit (evm : EVM.State) (locals : Store)
    (i refund deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hfit : refund.toNat + deposit.toNat < UInt256.size) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
        .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hnonneg : ¬ (((refund.toNat : Int) + (deposit.toNat : Int)) < 0) := by
    exact not_lt_of_ge (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  have hlt : ¬ ((2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int)) := by
    norm_num [UInt256.size] at hfit ⊢
    omega
  have hif :
      ¬ ((refund.toNat : Int) + (deposit.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int)) := by
    intro hcond
    rcases hcond with hneg | hge
    · exact hnonneg hneg
    · exact hlt hge
  simp only [uint256Int]
  rw [if_neg hif]
  rfl

theorem scratch_evalExpr_reveal_refund_add_deposit_revert (evm : EVM.State)
    (locals : Store) (i refund deposit : UInt256)
    (hbid :
      locals.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hover : UInt256.size ≤ refund.toNat + deposit.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
        .revert := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    scratch_evalExpr_reveal_bid_deposit evm locals i deposit hbid hdeposit,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hge : (2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int) := by
    norm_num [UInt256.size] at hover ⊢
    omega
  have hif :
      (refund.toNat : Int) + (deposit.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) + (deposit.toNat : Int) := by
    exact Or.inr hge
  simp only [uint256Int]
  rw [if_pos hif]

theorem scratch_evalExpr_reveal_refund_sub_value (evm : EVM.State) (locals : Store)
    (refund value : UInt256)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hle : value.toNat ≤ refund.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .sub (.var "refund") (.var "value"))) =
        .ok (.int (Int.ofNat (refund.toNat - value.toNat))) := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hsub_nonneg :
      ¬ (((refund.toNat : Int) - (value.toNat : Int)) < 0) := by
    omega
  have hsub_lt : ¬ ((2 : Int) ^ 256 ≤ (refund.toNat : Int) - (value.toNat : Int)) := by
    have hrefund_lt : refund.toNat < UInt256.size := refund.val.isLt
    norm_num [UInt256.size] at hrefund_lt ⊢
    omega
  have hif :
      ¬ ((refund.toNat : Int) - (value.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) - (value.toNat : Int)) := by
    intro hcond
    rcases hcond with hneg | hge
    · exact hsub_nonneg hneg
    · exact hsub_lt hge
  simp only [uint256Int]
  rw [if_neg hif]
  change EvalResult.ok (Value.int ((refund.toNat : Int) - (value.toNat : Int))) =
    EvalResult.ok (Value.int (Int.ofNat (refund.toNat - value.toNat)))
  rw [← Int.ofNat_sub hle]
  rfl

theorem scratch_evalExpr_reveal_refund_sub_value_revert (evm : EVM.State) (locals : Store)
    (refund value : UInt256)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hlt : refund.toNat < value.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (u256 (.binary .sub (.var "refund") (.var "value"))) =
        .revert := by
  unfold u256
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "refund" (Int.ofNat refund.toNat) hrefund,
    evalExpr_reveal_var_int evm locals "value" (Int.ofNat value.toNat) hvalue,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hneg : (refund.toNat : Int) - (value.toNat : Int) < 0 := by
    omega
  have hif :
      (refund.toNat : Int) - (value.toNat : Int) < 0 ∨
        (2 : Int) ^ 256 ≤ (refund.toNat : Int) - (value.toNat : Int) := Or.inl hneg
  simp only [uint256Int]
  rw [if_pos hif]

theorem scratch_evalExpr_reveal_i_add_one (evm : EVM.State) (locals : Store)
    (i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hfit : i.toNat + 1 < UInt256.size) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .add (.var "i") (.intLit 1)) =
        .ok (.int (Int.ofNat (i + ⟨1⟩).toNat)) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr?, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]
  have hadd : (i + ⟨1⟩).toNat = i.toNat + 1 := add1_toNat hfit
  rw [hadd]
  norm_num

theorem scratch_revealLoopPostStep (evm : EVM.State) (locals : Store) (i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hfit : i.toNat + 1 < UInt256.size) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
      (.ok { contract := blindAuctionContract,
              locals := locals.insert "i" (.int (Int.ofNat (i + ⟨1⟩).toNat)) } evm) := by
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  exact ExecStmt.assign
    (scratch_evalExpr_reveal_i_add_one evm locals i hi hfit)
    (scratch_assign_local_value evm locals "i" (.int (Int.ofNat i.toNat))
      (.int (Int.ofNat (i + ⟨1⟩).toNat)) hi)

def scratch_revealSourceLoopInv (len : UInt256)
    (Rest : ℕ → UInt256 → UInt256 → Store → EVM.State → Prop)
    (v : ℕ) (locals : Store) (evm : EVM.State) : Prop :=
  ∃ i refund,
    locals.get? "i" = some (.int (Int.ofNat i.toNat)) ∧
    locals.get? "length" = some (.int (Int.ofNat len.toNat)) ∧
    locals.get? "refund" = some (.int (Int.ofNat refund.toNat)) ∧
    i.toNat + v = len.toNat ∧
    i.toNat ≤ len.toNat ∧
    Rest v i refund locals evm

theorem scratch_revealForLoop_from_step (len : UInt256)
    (Rest : ℕ → UInt256 → UInt256 → Store → EVM.State → Prop)
    (hstep : ∀ (v : ℕ) (L : Store) (evm : EVM.State) (i refund : UInt256),
        scratch_revealSourceLoopInv len Rest (v + 1) L evm →
        L.get? "i" = some (.int (Int.ofNat i.toNat)) →
        L.get? "refund" = some (.int (Int.ofNat refund.toNat)) →
        ∃ L1 evm1,
          (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts (.ok { contract := blindAuctionContract, locals := L1 }
                evm1) ∨
            ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts
                (.continue { contract := blindAuctionContract, locals := L1 } evm1)) ∧
          ∃ L2 evm2,
            ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1
              scratch_revealLoopPostStmts (.ok { contract := blindAuctionContract, locals := L2 }
                evm2) ∧
            scratch_revealSourceLoopInv len Rest v L2 evm2) :
    ∀ v L evm, scratch_revealSourceLoopInv len Rest v L evm →
      ∃ L' evm',
        ExecForLoop blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L' } evm') ∧
        scratch_revealSourceLoopInv len Rest 0 L' evm' := by
  refine execFor_var_state_continue (cfg := blindAuctionConfig) (C := blindAuctionContract)
    (condExpr := .binary .lt (.var "i") (.var "length"))
    (post := scratch_revealLoopPostStmts) (body := scratch_revealLoopBodyStmts)
    (P := scratch_revealSourceLoopInv len Rest) ?_ ?_ ?_
  · intro L evm hP
    rcases hP with ⟨i, refund, hi, hlen, _hrefund, hvar, _hle, _hrest⟩
    exact scratch_evalExpr_reveal_loop_cond_false_of_get evm L len i hi hlen (by omega)
  · intro v L evm hP
    rcases hP with ⟨i, refund, hi, hlen, _hrefund, hvar, _hle, _hrest⟩
    exact scratch_evalExpr_reveal_loop_cond_true_of_get evm L len i hi hlen (by omega)
  · intro v L evm hP
    rcases hP with ⟨i, refund, hi, hlen, hrefund, hvar, hle, hrest⟩
    exact hstep v L evm i refund ⟨i, refund, hi, hlen, hrefund, hvar, hle, hrest⟩ hi
      hrefund

theorem scratch_blindAuctionRevealBodyReturns_callSuccess_fromLoop
    (evm evmLoop evm' : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok
          ({ contract := blindAuctionContract,
             locals := scratch_revealLoopStore callargs len refund i } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (true, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        (.returned
          ({ contract := blindAuctionContract,
             locals := scratch_revealCallStore callargs len refund i true out } : Frame)
          evm' none) := by
    let lengthFrame : Frame :=
      { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
    let refundFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealRefundStore callargs len ⟨0⟩ }
    let initLoopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
    let loopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len refund i }
    let finalFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealCallStore callargs len refund i true out }
    refine ExecFuncBody.execBlockOK ?_
    unfold revealTransition
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
    have hlengthEval :
        evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
          evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
      exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
    refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
    change ExecBlock blindAuctionConfig lengthFrame evm
      (List.drop 4 revealTransition.body)
      (.ok finalFrame evm')
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "values" values len ?_
          (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hvalues
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
          (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hfakes
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
          (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hsecrets
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
    change ExecBlock blindAuctionConfig refundFrame evm
      [ scratch_revealForStmt,
        .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ]
      (.ok finalFrame evm')
    have hfor :
        ExecStmt blindAuctionConfig refundFrame evm
          scratch_revealForStmt
          (.ok loopFrame evmLoop) := by
      have hinit :
          ExecBlock blindAuctionConfig
            refundFrame evm
            [ .letDecl "i" (some uint256) (.intLit 0) ]
            (.ok initLoopFrame evm) := by
        refine ExecBlock.consNormal
          (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
        exact ExecBlock.nil
      exact ExecStmt.for hinit hloop
    refine ExecBlock.consNormal hfor ?_
    refine ExecBlock.consNormal
      (ExecStmt.lowLevelCallSuccess
        (evalExpr_reveal_sender evmLoop (scratch_revealLoopStore callargs len refund i))
        (evalExpr_reveal_refund evmLoop (scratch_revealLoopStore callargs len refund i)
          refund (scratch_revealLoopStore_refund_get callargs len refund i))
        (evalExpr_reveal_emptyBytes evmLoop (scratch_revealLoopStore callargs len refund i))
        hcall) ?_
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (scratch_evalExpr_reveal_success evm' callargs len refund i true out))
      ExecBlock.nil

theorem scratch_blindAuctionRevealBodyReverts_callFailure_fromLoop
    (evm evmLoop evm' : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok
          ({ contract := blindAuctionContract,
             locals := scratch_revealLoopStore callargs len refund i } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (false, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        .reverted := by
    let lengthFrame : Frame :=
      { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
    let refundFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealRefundStore callargs len ⟨0⟩ }
    let initLoopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
    let loopFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_revealLoopStore callargs len refund i }
    refine ExecFuncBody.execBlockRevert ?_
    unfold revealTransition
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
    have hlengthEval :
        evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
          evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
      exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
    refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
    change ExecBlock blindAuctionConfig lengthFrame evm
      (List.drop 4 revealTransition.body) .reverted
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "values" values len ?_
          (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hvalues
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
          (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hfakes
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_reveal_local_array_length_eq_var_true evm
          (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
          (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
    · unfold scratch_revealLengthStore
      rw [store_get_ne]
      · exact hsecrets
      · decide
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
    change ExecBlock blindAuctionConfig refundFrame evm
      [ scratch_revealForStmt,
        .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ]
      .reverted
    have hfor :
        ExecStmt blindAuctionConfig refundFrame evm
          scratch_revealForStmt
          (.ok loopFrame evmLoop) := by
      have hinit :
          ExecBlock blindAuctionConfig
            refundFrame evm
            [ .letDecl "i" (some uint256) (.intLit 0) ]
            (.ok initLoopFrame evm) := by
        refine ExecBlock.consNormal
          (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
        exact ExecBlock.nil
      exact ExecStmt.for hinit hloop
    refine ExecBlock.consNormal hfor ?_
    refine ExecBlock.consNormal
      (ExecStmt.lowLevelCallFailure
        (evalExpr_reveal_sender evmLoop (scratch_revealLoopStore callargs len refund i))
        (evalExpr_reveal_refund evmLoop (scratch_revealLoopStore callargs len refund i)
          refund (scratch_revealLoopStore_refund_get callargs len refund i))
        (evalExpr_reveal_emptyBytes evmLoop (scratch_revealLoopStore callargs len refund i))
        hcall) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (scratch_evalExpr_reveal_success evm' callargs len refund i false out))

theorem scratch_blindAuctionRevealBodyReturns_callSuccess_fromLoopOfLocals
    (evm evmLoop evm' : EVM.State) (callargs loopLocals : Store)
    (values fakes secrets : List Value) (len refund : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hrefund : loopLocals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok ({ contract := blindAuctionContract, locals := loopLocals } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (true, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        (.returned
          ({ contract := blindAuctionContract,
             locals := scratch_revealCallStoreOf loopLocals true out } : Frame)
          evm' none) := by
  let lengthFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
  let refundFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealRefundStore callargs len ⟨0⟩ }
  let initLoopFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
  refine ExecFuncBody.execBlockOK ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig lengthFrame evm
    (List.drop 4 revealTransition.body)
    (.ok
      ({ contract := blindAuctionContract,
         locals := scratch_revealCallStoreOf loopLocals true out } : Frame) evm')
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "values" values len ?_
        (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hvalues
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
        (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hfakes
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
        (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hsecrets
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig refundFrame evm
    [ scratch_revealForStmt,
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok
      ({ contract := blindAuctionContract,
         locals := scratch_revealCallStoreOf loopLocals true out } : Frame) evm')
  have hfor :
      ExecStmt blindAuctionConfig refundFrame evm
        scratch_revealForStmt
        (.ok { contract := blindAuctionContract, locals := loopLocals } evmLoop) := by
    have hinit :
        ExecBlock blindAuctionConfig
          refundFrame evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok initLoopFrame evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_reveal_sender evmLoop loopLocals)
      (evalExpr_reveal_refund evmLoop loopLocals refund hrefund)
      (evalExpr_reveal_emptyBytes evmLoop loopLocals)
      hcall) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (scratch_evalExpr_reveal_success_of evm' loopLocals true out))
    ExecBlock.nil

theorem scratch_blindAuctionRevealBodyReverts_callFailure_fromLoopOfLocals
    (evm evmLoop evm' : EVM.State) (callargs loopLocals : Store)
    (values fakes secrets : List Value) (len refund : UInt256) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hrefund : loopLocals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts
        (.ok ({ contract := blindAuctionContract, locals := loopLocals } : Frame) evmLoop))
    (hcall :
      callViaEVM evmLoop (EVM.address evmLoop.executionEnv.source)
        (Int.ofNat refund.toNat) ByteArray.empty (false, evm', out)) :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
        .reverted := by
  let lengthFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
  let refundFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealRefundStore callargs len ⟨0⟩ }
  let initLoopFrame : Frame :=
    { contract := blindAuctionContract,
      locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig lengthFrame evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "values" values len ?_
        (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hvalues
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
        (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hfakes
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
        (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hsecrets
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig refundFrame evm
    [ scratch_revealForStmt,
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    .reverted
  have hfor :
      ExecStmt blindAuctionConfig refundFrame evm
        scratch_revealForStmt
        (.ok { contract := blindAuctionContract, locals := loopLocals } evmLoop) := by
    have hinit :
        ExecBlock blindAuctionConfig
          refundFrame evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok initLoopFrame evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_reveal_sender evmLoop loopLocals)
      (evalExpr_reveal_refund evmLoop loopLocals refund hrefund)
      (evalExpr_reveal_emptyBytes evmLoop loopLocals)
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (scratch_evalExpr_reveal_success_of evm' loopLocals false out))

theorem scratch_revealLoopBody_ok_noPlace (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hskipPlace : fake = true ∨ deposit.toNat < value.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret fake
  let L5 := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit fake
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using
      scratch_revealSecretStore_bid_get callargs evm len refund i value secret fake
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStore_refund_get callargs evm len refund i value secret fake
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStore, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_bid_get callargs evm len refund i value secret deposit fake
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_value_get callargs evm len refund i value secret deposit fake
  have hcondFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool false) := by
    cases fake with
    | false =>
        have hfakeL5 : L5.get? "fake" = some (.bool false) := by
          simpa [L5] using
            scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit
              false
        rcases hskipPlace with hfakeTrue | hlt
        · cases hfakeTrue
        · exact scratch_evalExpr_reveal_placeBid_cond_false_deposit evm L5 i value deposit
            hbidL5 hfakeL5 hvalueL5 hdeposit hlt
    | true =>
        have hfakeL5 : L5.get? "fake" = some (.bool true) := by
          simpa [L5] using
            scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit
              true
        exact scratch_evalExpr_reveal_placeBid_cond_false_fake evm L5 i value deposit
          hbidL5 hfakeL5 hvalueL5 hdeposit
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L5
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L5 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L5 i hbidL5
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L5 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L5 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hcondFalse ExecBlock.nil) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  exact scratch_revealLoopBody_prefix_exec evm callargs values fakes secrets len refund i value
    secret fake fakeRaw hbids hvalues hfakes hsecrets hlen hboundBids hboundValues
    hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_false (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceFalse : value.toNat ≤ high.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals :=
            (scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false)
              |>.insert "ok" (.bool false) }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret false
  let L5 := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false
  let L6 := L5.insert "ok" (.bool false)
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using
      scratch_revealSecretStore_bid_get callargs evm len refund i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStore_refund_get callargs evm len refund i value secret false
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStore, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_bid_get callargs evm len refund i value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_value_get callargs evm len refund i value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evm)
        (value := some (.bool false))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by
          simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using
            (scratch_blindAuctionPlaceBidBodyReturns_false evm evm.executionEnv.source value high
              hhigh hplaceFalse))
  have hokFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.var "ok") = .ok (.bool false) := by
    exact evalExpr_reveal_var_value evm L6 "ok" (.bool false) (by simp [L6])
  have hbidL6 :
      L6.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L6
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L6 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L6 i hbidL6
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    refine ExecBlock.consNormal hcall ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hokFalse ExecBlock.nil) ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L6 } evm) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L6 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L6 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evm) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [L6] using
    scratch_revealLoopBody_prefix_exec evm callargs values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_core (evm evmPB : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceBody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm
        (scratch_placeBidStore evm.executionEnv.source value) placeBidFn.body
        (.returned
          { contract := blindAuctionContract,
            locals := scratch_placeBidStore evm.executionEnv.source value }
          evmPB (some (.bool true))))
    (href : scratch_revealBidEvaledRef evmPB i = scratch_revealBidEvaledRef evm i) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStore callargs evm len refund i value secret deposit }
        (scratch_revealZeroBlindedState evmPB i)) := by
  let L4 := scratch_revealSecretStore callargs evm len refund i value secret false
  let L5 := scratch_revealRefundAddedStore callargs evm len refund i value secret deposit false
  let L6 := L5.insert "ok" (.bool true)
  let refundAdded : UInt256 := UInt256.ofNat (refund.toNat + deposit.toNat)
  let L7 := L6.insert "refund" (.int (Int.ofNat (refundAdded.toNat - value.toNat)))
  have hrefundAddedToNat : refundAdded.toNat = refund.toNat + deposit.toNat := by
    simpa [refundAdded] using ulit_toNat' (refund.toNat + deposit.toNat) hfit
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using
      scratch_revealSecretStore_bid_get callargs evm len refund i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStore_refund_get callargs evm len refund i value secret false
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStore, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_bid_get callargs evm len refund i value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_value_get callargs evm len refund i value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStore_fake_get callargs evm len refund i value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evmPB) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evmPB)
        (value := some (.bool true))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using hplaceBody)
  have hokTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.var "ok") = .ok (.bool true) := by
    exact evalExpr_reveal_var_value evmPB L6 "ok" (.bool true) (by simp [L6])
  have hrefundL6 :
      L6.get? "refund" = some (.int (Int.ofNat refundAdded.toNat)) := by
    simpa [L6, refundAdded, hrefundAddedToNat, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
        scratch_revealRefundAddedStore_refund_get callargs evm len refund i value secret deposit false
  have hvalueL6 :
      L6.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hvalueL5
  have hsubLe : value.toNat ≤ refundAdded.toNat := by
    rw [hrefundAddedToNat]
    omega
  have hsub :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (u256 (.binary .sub (.var "refund") (.var "value"))) =
          .ok (.int (Int.ofNat (refundAdded.toNat - value.toNat))) :=
    scratch_evalExpr_reveal_refund_sub_value evmPB L6 refundAdded value hrefundL6 hvalueL6
      hsubLe
  have hassignSub :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        .localVar { base := "refund" } (.int (Int.ofNat (refundAdded.toNat - value.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L7 }, evmPB) := by
    simpa [L7] using
      scratch_assign_local_value evmPB L6 "refund" (.int (Int.ofNat refundAdded.toNat))
        (.int (Int.ofNat (refundAdded.toNat - value.toNat))) hrefundL6
  have hbidL7 :
      L7.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evmPB i) bidStructTy) := by
    have hbidOrig :
        L7.get? "bidToCheck" =
          some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
      simpa [L7, L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
    simpa [href] using hbidOrig
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evmPB L7
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L7 },
            scratch_revealZeroBlindedState evmPB i) :=
    scratch_assign_reveal_blinded_zero evmPB L7 i hbidL7
  have hthenOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        [ .assign .localVar { base := "refund" }
            (u256 (.binary .sub (.var "refund") (.var "value"))) ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    exact ExecBlock.consNormal (ExecStmt.assign hsub hassignSub) ExecBlock.nil
  have hokIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.ite (.var "ok")
          [ .assign .localVar { base := "refund" }
              (u256 (.binary .sub (.var "refund") (.var "value"))) ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hokTrue hthenOk
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evmPB) hcall ?_
    exact ExecBlock.consNormal hokIte ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L7 }
          (scratch_revealZeroBlindedState evmPB i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L7 }
        (scratch_revealZeroBlindedState evmPB i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L7 })
      (evm' := evmPB) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [scratch_revealRefundPlacedStore, L7, L6, L5, refundAdded, hrefundAddedToNat] using
    scratch_revealLoopBody_prefix_exec evm callargs values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_zero (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high old : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStore callargs evm len refund i value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core evm evmPB callargs values fakes secrets
    len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes hsecrets
    hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm
    hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_zero evm evm.executionEnv.source value high old
        hhigh hold hlt hzero
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_revealBidEvaledRef_storageStore]

theorem scratch_revealLoopBody_ok_placeBid_true_nonzero (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value)
    (len refund i value secret blinded deposit high old pending : UInt256)
    (oldAddr : AccountAddress) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStore callargs evm len refund i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len refund i }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStore callargs evm len refund i value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder
            (scratch_placeBidAfterHigh
              (scratch_placeBidAfterPending evm oldAddr
                (UInt256.ofNat (pending.toNat + high.toNat))) value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder
      (scratch_placeBidAfterHigh
        (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))) value)
      evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core evm evmPB callargs values fakes secrets
    len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes hsecrets
    hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm
    hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_nonzero evm evm.executionEnv.source oldAddr
        value high old pending hhigh hold holdAddr hpending hlt hnonzero hsum
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_placeBidAfterPending, scratch_revealBidEvaledRef_storageStore]

/-! ### Generic source loop body facts over arbitrary locals -/

def scratch_revealBidToCheckStoreOf (locals : Store) (evm : EVM.State)
    (i : UInt256) : Store :=
  locals.insert "bidToCheck" (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy)

def scratch_revealValueStoreOf (locals : Store) (evm : EVM.State)
    (i value : UInt256) : Store :=
  (scratch_revealBidToCheckStoreOf locals evm i).insert "value"
    (.int (Int.ofNat value.toNat))

def scratch_revealFakeStoreOf (locals : Store) (evm : EVM.State)
    (i value : UInt256) (fake : Bool) : Store :=
  (scratch_revealValueStoreOf locals evm i value).insert "fake" (.bool fake)

def scratch_revealSecretStoreOf (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) : Store :=
  (scratch_revealFakeStoreOf locals evm i value fake).insert "secret"
    (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))

def scratch_revealRefundAddedStoreOf (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) : Store :=
  (scratch_revealSecretStoreOf locals evm i value secret fake).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat)))

def scratch_revealRefundPlacedStoreOf (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) : Store :=
  ((scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false).insert
      "ok" (.bool true)).insert "refund"
    (.int (Int.ofNat (refund.toNat + deposit.toNat - value.toNat)))

theorem scratch_revealBidToCheckStoreOf_bid_get (locals : Store) (evm : EVM.State)
    (i : UInt256) :
    (scratch_revealBidToCheckStoreOf locals evm i).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealBidToCheckStoreOf
  rw [store_get_self]

theorem scratch_evalStorageRef_reveal_bid_ok_of_get (evm : EVM.State) (locals : Store)
    (i len : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i) := by
  have hbounds := scratch_revealBid_arrayIndexInBounds_ok evm i len hlen hbound
  simp only [bidElemRef, sender, evalStorageRef, evalStorageRefSteps.eq_def,
    evalStorageRefStep.eq_def, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, List.nil_append, scratch_revealBidEvaledRef, hi]
  rw [hbounds]

theorem scratch_resolveStorageRef_reveal_bid_ok_of_get (evm : EVM.State) (locals : Store)
    (i len : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    resolveStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (bidElemRef sender (.var "i")) =
        .ok (scratch_revealBidEvaledRef evm i, bidStructTy) := by
  exact resolveStorageRef?_ok hbids
    (scratch_evalStorageRef_reveal_bid_ok_of_get evm locals i len hi hlen hbound)
    (scratch_revealBid_storageType evm i)

theorem scratch_letStorage_reveal_bidToCheck_of_get (evm : EVM.State) (locals : Store)
    (i len : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hbound : i.toNat < len.toNat) :
    ExecStmt blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (.letStorage "bidToCheck" (bidElemRef sender (.var "i")))
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealBidToCheckStoreOf locals evm i }
        evm) := by
  exact ExecStmt.letStorage
    (scratch_resolveStorageRef_reveal_bid_ok_of_get evm locals i len hbids hi hlen hbound)

theorem scratch_revealSecretStoreOf_bid_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "bidToCheck" =
      some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf scratch_revealValueStoreOf
    scratch_revealBidToCheckStoreOf
  rw [store_get_ne, store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide
  · decide

theorem scratch_revealSecretStoreOf_value_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "value" =
      some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf scratch_revealValueStoreOf
  rw [store_get_ne, store_get_ne, store_get_self]
  · decide
  · decide

theorem scratch_revealSecretStoreOf_fake_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "fake" =
      some (.bool fake) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf
  rw [store_get_ne, store_get_self]
  decide

theorem scratch_revealSecretStoreOf_refund_get (locals : Store) (evm : EVM.State)
    (i refund value secret : UInt256) (fake : Bool)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat))) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "refund" =
      some (.int (Int.ofNat refund.toNat)) := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf scratch_revealValueStoreOf
    scratch_revealBidToCheckStoreOf
  rw [store_get_ne, store_get_ne, store_get_ne, store_get_ne]
  · exact hrefund
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_bid_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_ne]
  · exact scratch_revealSecretStoreOf_bid_get locals evm i value secret fake
  · decide

theorem scratch_revealRefundAddedStoreOf_value_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "value" = some (.int (Int.ofNat value.toNat)) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_ne]
  · exact scratch_revealSecretStoreOf_value_get locals evm i value secret fake
  · decide

theorem scratch_revealRefundAddedStoreOf_fake_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "fake" = some (.bool fake) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_ne]
  · exact scratch_revealSecretStoreOf_fake_get locals evm i value secret fake
  · decide

theorem scratch_revealRefundAddedStoreOf_refund_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
      "refund" = some (.int (Int.ofNat (refund.toNat + deposit.toNat))) := by
  unfold scratch_revealRefundAddedStoreOf
  rw [store_get_self]

theorem scratch_revealLoopBody_prefix_exec_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret : UInt256)
    (fake : Bool) (fakeRaw : Value) {result : ExecResult}
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake }
        evm (List.drop 4 scratch_revealLoopBodyStmts) result) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts result := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck_of_get evm locals i len hbids hi hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStoreOf locals evm i
  let L2 := scratch_revealValueStoreOf locals evm i value
  let L3 := scratch_revealFakeStoreOf locals evm i value fake
  let L4 := scratch_revealSecretStoreOf locals evm i value secret fake
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hvalues
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hi
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hfakes
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hi
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .ok (.bool fake) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L2 "fakes" fakes i
      fakeRaw (.bool fake) hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  refine ExecBlock.consNormal (ExecStmt.letDecl hfakeEval) ?_
  have hsecretsL3 : L3.get? "secrets" = some (.array secrets) := by
    simpa [L3, scratch_revealFakeStoreOf, scratch_revealValueStoreOf, L1,
      scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hsecrets
  have hiL3 : L3.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L3, scratch_revealFakeStoreOf, scratch_revealValueStoreOf, L1,
      scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hi
  have hsecretEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L3 } evm
        (.index (.var "secrets") (.var "i")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L3 "secrets" secrets i
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      hsecretsL3 hiL3 hboundSecrets hsecretLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hsecretEval) ?_
  simpa [L4, scratch_revealLoopBodyStmts] using htail

theorem scratch_revealLoopBody_revert_fake_invalid_of_get (evm : EVM.State)
    (locals : Store) (values fakes secrets : List Value) (len i value : UInt256)
    (fakeRaw : Value)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .revert) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts .reverted := by
  unfold scratch_revealLoopBodyStmts
  refine ExecBlock.consNormal
    (scratch_letStorage_reveal_bidToCheck_of_get evm locals i len hbids hi hlen hboundBids) ?_
  let L1 := scratch_revealBidToCheckStoreOf locals evm i
  let L2 := scratch_revealValueStoreOf locals evm i value
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hvalues
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L1, scratch_revealBidToCheckStoreOf, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using hi
  have hvalueEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm
        (.index (.var "values") (.var "i")) =
          .ok (.int (Int.ofNat value.toNat)) := by
    exact scratch_evalExpr_reveal_local_array_index_norm evm L1 "values" values i
      (.int (Int.ofNat value.toNat)) (.int (Int.ofNat value.toNat)) hvaluesL1 hiL1
      hboundValues hvalueLookup (by simp [normalizeRawBoolWord?])
  refine ExecBlock.consNormal (ExecStmt.letDecl hvalueEval) ?_
  have hfakesL2 : L2.get? "fakes" = some (.array fakes) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hfakes
  have hiL2 : L2.get? "i" = some (.int (Int.ofNat i.toNat)) := by
    simpa [L2, scratch_revealValueStoreOf, L1, scratch_revealBidToCheckStoreOf,
      Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hi
  have hfakeEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L2 } evm
        (.index (.var "fakes") (.var "i")) = .revert := by
    exact scratch_evalExpr_reveal_local_array_index_revert evm L2 "fakes" fakes i fakeRaw
      hfakesL2 hiL2 hboundFakes hfakeLookup hfakeNorm
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hfakeEval)

theorem scratch_revealLoopBody_ok_noPlace_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hskipPlace : fake = true ∨ deposit.toNat < value.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret fake
  let L5 := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret fake
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret fake hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStoreOf, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_bid_get locals evm i refund value secret deposit fake
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_value_get locals evm i refund value secret deposit fake
  have hcondFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool false) := by
    cases fake with
    | false =>
        have hfakeL5 : L5.get? "fake" = some (.bool false) := by
          simpa [L5] using
            scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit
              false
        rcases hskipPlace with hfakeTrue | hlt
        · cases hfakeTrue
        · exact scratch_evalExpr_reveal_placeBid_cond_false_deposit evm L5 i value deposit
            hbidL5 hfakeL5 hvalueL5 hdeposit hlt
    | true =>
        have hfakeL5 : L5.get? "fake" = some (.bool true) := by
          simpa [L5] using
            scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit true
        exact scratch_evalExpr_reveal_placeBid_cond_false_fake evm L5 i value deposit
          hbidL5 hfakeL5 hvalueL5 hdeposit
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L5
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L5 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L5 i hbidL5
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L5 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L5 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hcondFalse ExecBlock.nil) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  exact scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i
    value secret fake fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
    hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_continue_hash_mismatch_of_get (evm : EVM.State)
    (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded : UInt256)
    (fake : Bool) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (hne : EVM.Word.toBytesBE blinded ≠ hashBytes) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.continue
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake }
        evm) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret fake
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret fake
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool true) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_true evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) hne
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.continue { contract := blindAuctionContract, locals := L4 } evm) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.continue { contract := blindAuctionContract, locals := L4 } evm)
    refine ExecBlock.consContinue ?_
    refine ExecStmt.iteTrue hguard ?_
    exact ExecBlock.consContinue ExecStmt.continue
  exact scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i
    value secret fake fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
    hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_false_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceFalse : value.toNat ≤ high.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals :=
            (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false)
              |>.insert "ok" (.bool false) }
        (scratch_revealZeroBlindedState evm i)) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret false
  let L5 := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false
  let L6 := L5.insert "ok" (.bool false)
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret false hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStoreOf, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_bid_get locals evm i refund value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_value_get locals evm i refund value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evm)
        (value := some (.bool false))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by
          simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using
            (scratch_blindAuctionPlaceBidBodyReturns_false evm evm.executionEnv.source value high
              hhigh hplaceFalse))
  have hokFalse :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.var "ok") = .ok (.bool false) := by
    exact evalExpr_reveal_var_value evm L6 "ok" (.bool false) (by simp [L6])
  have hbidL6 :
      L6.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evm L6
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evm
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L6 },
            scratch_revealZeroBlindedState evm i) :=
    scratch_assign_reveal_blinded_zero evm L6 i hbidL6
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L6 } evm) := by
    refine ExecBlock.consNormal hcall ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hokFalse ExecBlock.nil) ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L6 } evm) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L6 }
          (scratch_revealZeroBlindedState evm i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L6 }
        (scratch_revealZeroBlindedState evm i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evm) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [L6] using
    scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_core_of_get (evm evmPB : EVM.State)
    (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceBody :
      ExecTransitionBody blindAuctionConfig blindAuctionContract evm
        (scratch_placeBidStore evm.executionEnv.source value) placeBidFn.body
        (.returned
          { contract := blindAuctionContract,
            locals := scratch_placeBidStore evm.executionEnv.source value }
          evmPB (some (.bool true))))
    (href : scratch_revealBidEvaledRef evmPB i = scratch_revealBidEvaledRef evm i) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit }
        (scratch_revealZeroBlindedState evmPB i)) := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret false
  let L5 := scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit false
  let L6 := L5.insert "ok" (.bool true)
  let refundAdded : UInt256 := UInt256.ofNat (refund.toNat + deposit.toNat)
  let L7 := L6.insert "refund" (.int (Int.ofNat (refundAdded.toNat - value.toNat)))
  have hrefundAddedToNat : refundAdded.toNat = refund.toNat + deposit.toNat := by
    simpa [refundAdded] using ulit_toNat' (refund.toNat + deposit.toNat) hfit
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret false
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret false hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .ok (.int (Int.ofNat (refund.toNat + deposit.toNat))) :=
    scratch_evalExpr_reveal_refund_add_deposit evm L4 i refund deposit hbidL4 hrefundL4
      hdeposit hfit
  have hassignRefund :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        .localVar { base := "refund" } (.int (Int.ofNat (refund.toNat + deposit.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L5 }, evm) := by
    simpa [L5, scratch_revealRefundAddedStoreOf, L4] using
      scratch_assign_local_value evm L4 "refund" (.int (Int.ofNat refund.toNat))
        (.int (Int.ofNat (refund.toNat + deposit.toNat))) hrefundL4
  have hbidL5 :
      L5.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_bid_get locals evm i refund value secret deposit false
  have hvalueL5 :
      L5.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_value_get locals evm i refund value secret deposit false
  have hfakeL5 : L5.get? "fake" = some (.bool false) := by
    simpa [L5] using
      scratch_revealRefundAddedStoreOf_fake_get locals evm i refund value secret deposit false
  have hcondTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.binary .and (.unary .not (.var "fake"))
          (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value"))) =
          .ok (.bool true) :=
    scratch_evalExpr_reveal_placeBid_cond_true evm L5 i value deposit hbidL5 hfakeL5
      hvalueL5 hdeposit hdepositGe
  have hcall :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.internalCall "placeBid" [sender, .var "value"] "ok")
        (.ok { contract := blindAuctionContract, locals := L6 } evmPB) := by
    let calleeFrame : Frame :=
      { contract := blindAuctionContract,
        locals := scratch_placeBidStore evm.executionEnv.source value }
    simpa [L6] using
      ExecStmt.internalCallReturn
        (cfg := blindAuctionConfig)
        (solm := { contract := blindAuctionContract, locals := L5 })
        (evm := evm)
        (name := "placeBid") (retVar := "ok")
        (args := [sender, .var "value"])
        (argVals := [.address evm.executionEnv.source, .int (Int.ofNat value.toNat)])
        (callee := placeBidFn.toCallable)
        (locals := scratch_placeBidStore evm.executionEnv.source value)
        (calleeSolm := calleeFrame)
        (calleeEvm := evmPB)
        (value := some (.bool true))
        (scratch_evalExprs_reveal_placeBid_args evm L5 value hvalueL5)
        scratch_placeBid_lookup
        (by simpa [FunctionDecl.toCallable] using
          scratch_placeBid_bind evm.executionEnv.source value)
        (by simpa [ExecTransitionBody, FunctionDecl.toCallable, calleeFrame] using hplaceBody)
  have hokTrue :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.var "ok") = .ok (.bool true) := by
    exact evalExpr_reveal_var_value evmPB L6 "ok" (.bool true) (by simp [L6])
  have hrefundL6 :
      L6.get? "refund" = some (.int (Int.ofNat refundAdded.toNat)) := by
    simpa [L6, refundAdded, hrefundAddedToNat, Std.HashMap.getElem?_insert,
      Std.HashMap.get?_eq_getElem?] using
        scratch_revealRefundAddedStoreOf_refund_get locals evm i refund value secret deposit false
  have hvalueL6 :
      L6.get? "value" = some (.int (Int.ofNat value.toNat)) := by
    simpa [L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hvalueL5
  have hsubLe : value.toNat ≤ refundAdded.toNat := by
    rw [hrefundAddedToNat]
    omega
  have hsub :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (u256 (.binary .sub (.var "refund") (.var "value"))) =
          .ok (.int (Int.ofNat (refundAdded.toNat - value.toNat))) :=
    scratch_evalExpr_reveal_refund_sub_value evmPB L6 refundAdded value hrefundL6 hvalueL6
      hsubLe
  have hassignSub :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        .localVar { base := "refund" } (.int (Int.ofNat (refundAdded.toNat - value.toNat))) =
          .ok ({ contract := blindAuctionContract, locals := L7 }, evmPB) := by
    simpa [L7] using
      scratch_assign_local_value evmPB L6 "refund" (.int (Int.ofNat refundAdded.toNat))
        (.int (Int.ofNat (refundAdded.toNat - value.toNat))) hrefundL6
  have hbidL7 :
      L7.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evmPB i) bidStructTy) := by
    have hbidOrig :
        L7.get? "bidToCheck" =
          some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
      simpa [L7, L6, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?] using hbidL5
    simpa [href] using hbidOrig
  have hzero :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        (.cast (.intLit 0) bytes32St) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) :=
    scratch_evalExpr_reveal_cast_zero_bytes32 evmPB L7
  have hassignZero :
      assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := L7 } evmPB
        .storage (aliasF "bidToCheck" "blindedBid")
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (EVM.Word.ofNat 0))) =
          .ok ({ contract := blindAuctionContract, locals := L7 },
            scratch_revealZeroBlindedState evmPB i) :=
    scratch_assign_reveal_blinded_zero evmPB L7 i hbidL7
  have hthenOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        [ .assign .localVar { base := "refund" }
            (u256 (.binary .sub (.var "refund") (.var "value"))) ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    exact ExecBlock.consNormal (ExecStmt.assign hsub hassignSub) ExecBlock.nil
  have hokIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L6 } evmPB
        (.ite (.var "ok")
          [ .assign .localVar { base := "refund" }
              (u256 (.binary .sub (.var "refund") (.var "value"))) ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hokTrue hthenOk
  have hplaceThen :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        [ .internalCall "placeBid" [sender, .var "value"] "ok",
          .ite (.var "ok")
            [ .assign .localVar { base := "refund" }
                (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) := by
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L6 })
      (evm' := evmPB) hcall ?_
    exact ExecBlock.consNormal hokIte ExecBlock.nil
  have hplaceIte :
      ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := L5 } evm
        (.ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [])
        (.ok { contract := blindAuctionContract, locals := L7 } evmPB) :=
    ExecStmt.iteTrue hcondTrue hplaceThen
  have htail :
      ExecBlock blindAuctionConfig
        { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts)
        (.ok { contract := blindAuctionContract, locals := L7 }
          (scratch_revealZeroBlindedState evmPB i)) := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      (.ok { contract := blindAuctionContract, locals := L7 }
        (scratch_revealZeroBlindedState evmPB i))
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hadd hassignRefund) ?_
    refine ExecBlock.consNormal (solm' := { contract := blindAuctionContract, locals := L7 })
      (evm' := evmPB) hplaceIte ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignZero) ExecBlock.nil
  simpa [scratch_revealRefundPlacedStoreOf, L7, L6, L5, refundAdded, hrefundAddedToNat] using
    scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i value
      secret false fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_ok_placeBid_true_zero_of_get (evm : EVM.State) (locals : Store)
    (values fakes secrets : List Value) (len refund i value secret blinded deposit high old : UInt256)
    (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core_of_get evm evmPB locals values fakes
    secrets len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes
    hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup
    hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_zero evm evm.executionEnv.source value high old
        hhigh hold hlt hzero
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_revealBidEvaledRef_storageStore]

theorem scratch_revealLoopBody_ok_placeBid_true_nonzero_of_get (evm : EVM.State)
    (locals : Store) (values fakes secrets : List Value)
    (len refund i value secret blinded deposit high old pending : UInt256)
    (oldAddr : AccountAddress) (fakeRaw : Value) (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret false } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hsum : pending.toNat + high.toNat < UInt256.size) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts
      (.ok
        { contract := blindAuctionContract,
          locals := scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit }
        (scratch_revealZeroBlindedState
          (scratch_placeBidAfterBidder
            (scratch_placeBidAfterHigh
              (scratch_placeBidAfterPending evm oldAddr
                (UInt256.ofNat (pending.toNat + high.toNat))) value)
            evm.executionEnv.source) i)) := by
  let evmPB :=
    scratch_placeBidAfterBidder
      (scratch_placeBidAfterHigh
        (scratch_placeBidAfterPending evm oldAddr
          (UInt256.ofNat (pending.toNat + high.toNat))) value)
      evm.executionEnv.source
  refine scratch_revealLoopBody_ok_placeBid_true_core_of_get evm evmPB locals values fakes
    secrets len refund i value secret blinded deposit fakeRaw hashBytes hbids hvalues hfakes
    hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup
    hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit hhash heq hfit hdepositGe ?_ ?_
  · simpa [evmPB] using
      scratch_blindAuctionPlaceBidBodyReturns_true_nonzero evm evm.executionEnv.source oldAddr
        value high old pending hhigh hold holdAddr hpending hlt hnonzero hsum
  · simp [evmPB, scratch_placeBidAfterBidder, scratch_placeBidAfterHigh,
      scratch_placeBidAfterPending, scratch_revealBidEvaledRef_storageStore]

end BlindAuction
