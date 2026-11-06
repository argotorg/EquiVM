import Benchmarks.Midnight.TickLibWrapper.TickToPrice

/-!
# TickLibWrapper `priceToTick(uint256,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
binary-search body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 168; reach lemma `tickLibWrapperReachPriceToTickBody`.

`priceToTick_body(price, spacing)` requires `price ≤ 1e18`, then binary-searches
`low ∈ [0, 6744]` with `high`, calling `tickToPrice_body(mid)` each iteration via the shared
`476 → 486 → wExp-tail → 523 → 446 → 453 → 570 → 319` path, and finally returns the
`inRange`-checked `(low + spacing - 1) / spacing * spacing` tail through the shared
checked-division block `446 → 453` and the `253 → 270` mul-check/return epilogue.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight.TickLibWrapper

set_option maxRecDepth 2000000

private abbrev uint256T : IntType := .uint ⟨256, by decide⟩
private abbrev uint256S : StorageType := .elem (.int uint256T)
private abbrev sint256T : IntType := .sint ⟨256, by decide⟩

/-- `priceToTick_body`'s FunctionDecl (second internal function). -/
abbrev priceToTickBodyDecl : FunctionDecl := contract.functions[2]!

/-- `priceToTick_body`'s spec body as emitted. -/
theorem p2tBodyDecl_body_eq : priceToTickBodyDecl.body =
    [.require (.binary .le (.var "price") (.intLit 1000000000000000000)),
     .letDecl "low" none (.intLit 0),
     .letDecl "high" none (.intLit 6744),
     .while (.binary .ne (.var "low") (.var "high"))
       [.letDecl "mid" none
         (.binary .div
           (.cast (.binary .add (.var "low") (.var "high")) uint256S)
           (.intLit 2)),
        .internalCall "tickToPrice_body" [.var "mid"] "__c0",
        .ite (.binary .lt (.var "__c0") (.var "price"))
          [.assign .localVar { base := "low", steps := [] }
            (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
          [.assign .localVar { base := "high", steps := [] } (.var "mid")]],
     .return [.binary .mul
       (.inRange uint256T
         (.binary .div
           (.inRange uint256T
             (.binary .sub
               (.inRange uint256T
                 (.binary .add (.var "low") (.var "spacing")))
               (.intLit 1)))
           (.var "spacing")))
       (.var "spacing")]] := rfl

/-- The spec result of `priceToTick_body`: `(low + spacing - 1) / spacing * spacing`
    evaluated under the `inRange`/division guards (which revert out of range or on `spacing = 0`,
    matching the EVM panic paths at 221/233/244+446). -/
def pttResult (low spacing : Int) : Int := ((low + spacing - 1) / spacing) * spacing

/-! ## Calldata decode -/

/-- Two `uint256` words decode to `price`/`spacing` when both arg words follow the selector
    and the calldata is under the huge-length bound. -/
theorem decodeScalarWords_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeScalarWords? [abiUInt256, abiUInt256] bytes 0 =
      some [.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_uint256_ok (start := 0) (by simpa using hlen0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 32) hlen32]
  rfl

theorem decodeScalarWords_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [abiUInt256, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_uint256_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]; omega
    have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_uint256_ok (start := 0) (by simpa using htake0)]
    simp only [Option.bind, bind]
    rw [decodeScalarWord_uint256_none_short (start := 32) htake32n]

theorem p2tDecode_ok {cd : ByteArray} (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    config.externalABI.decodeCalldata? (priceToTickTransition.params.map Param.name)
      (transitionSignature priceToTickTransition).paramTypes cd =
      some (((∅ : Store).insert "price"
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert "spacing"
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  show decodeCalldataWithMode .modern _ _ cd = _
  show decodeCalldata ["price", "spacing"] [abiUInt256, abiUInt256] cd = _
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := ["price", "spacing"])
    (types := [abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_uint256_uint256_ok (bytes := cd.toList.drop 4) htake4 htake36']
  change decodeCalldata.insertValues ["price", "spacing"]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Store).insert "price"
      (.int (Int.ofNat (calldataWord cd 4).toNat))).insert "spacing"
      (.int (Int.ofNat (calldataWord cd 36).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]

theorem p2tDecode_none {cd : ByteArray} (hsz4 : 4 ≤ cd.size)
    (h : cd.size < 68 ∨ 2 ^ 255 + 4 ≤ cd.size) :
    config.externalABI.decodeCalldata? (priceToTickTransition.params.map Param.name)
      (transitionSignature priceToTickTransition).paramTypes cd = none := by
  show decodeCalldataWithMode .modern _ _ cd = _
  show decodeCalldata ["price", "spacing"] [abiUInt256, abiUInt256] cd = _
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := ["price", "spacing"])
    (types := [abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rcases h with hs | hb
  · rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
    rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
    rw [decodeScalarWords_uint256_uint256_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]; omega)]
  · rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
    rw [if_pos]
    exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

/-! ## Stele-side body

`priceToTick_body`: `require price ≤ 1e18`; `low := 0`, `high := 6744`;
`while (low ≠ high)` binary-search via internal `tickToPrice_body` calls; then the
`inRange`-checked `(low + spacing - 1) / spacing * spacing` tail. -/

/-- Plain-path local assignment: `.assign .localVar { base := name }` writes `value` into the
    locals (root-path, `steps = []`).  Frame-general version of `assignLocalVarBase_ok`. -/
theorem assignLocalBase_ok {cfg : Config} {F : Frame} {evm : EVM.State} {locals : Store}
    {name : Ident} {old value : Value}
    (hget : locals.get? name = some old) :
    assignStorageRef? cfg { F with locals := locals } evm .localVar { base := name, steps := [] }
        value = .ok ({ F with locals := locals.insert name value }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  rw [hget]

/-- A `while` loop indexed by the measure `high - low`: at every iteration either the body
    reverts (propagating to the `while`) or one body pass lowers the measure.  The loop then
    either reaches a store where `low = high`, or reverts. -/
theorem execWhile_revert {cfg : Config} {F : Frame} {evm : EVM.State}
    {cond : Expr} {body : List Stmt}
    (P : ℕ → ℕ → Store → Prop)
    (hfalse : ∀ low high L, P low high L → low = high →
      evalExpr? cfg { F with locals := L } evm cond = .ok (.bool false))
    (htrue : ∀ low high L, P low high L → low ≠ high →
      evalExpr? cfg { F with locals := L } evm cond = .ok (.bool true))
    (hstep : ∀ low high L, P low high L → low < high →
      ExecBlock cfg { F with locals := L } evm body .reverted ∨
      ∃ low' high' L', ExecBlock cfg { F with locals := L } evm body
          (.ok { F with locals := L' } evm) ∧
        P low' high' L' ∧ low' ≤ high' ∧ high' - low' < high - low) :
    ∀ low high L, P low high L → low ≤ high →
      (∃ low' high' L', ExecStmt cfg { F with locals := L } evm (.while cond body)
          (.ok { F with locals := L' } evm) ∧ low' = high' ∧ P low' high' L') ∨
      ExecStmt cfg { F with locals := L } evm (.while cond body) .reverted := by
  intro low high L hP hle
  have key : ∀ n low high L, high - low ≤ n → P low high L → low ≤ high →
      (∃ low' high' L', ExecStmt cfg { F with locals := L } evm (.while cond body)
          (.ok { F with locals := L' } evm) ∧ low' = high' ∧ P low' high' L') ∨
      ExecStmt cfg { F with locals := L } evm (.while cond body) .reverted := by
    intro n
    induction n with
    | zero =>
      intro low high L hd hP hle
      left
      have heq : low = high := by omega
      exact ⟨low, high, L, ExecStmt.whileFalse (hfalse low high L hP heq), heq, hP⟩
    | succ n ih =>
      intro low high L hd hP hle
      by_cases heq : low = high
      · left; exact ⟨low, high, L, ExecStmt.whileFalse (hfalse low high L hP heq), heq, hP⟩
      · have hlt : low < high := by omega
        rcases hstep low high L hP hlt with hrev | ⟨low', high', L', hb, hP', hle', hdec⟩
        · right; exact ExecStmt.whileRevert (htrue low high L hP heq) hrev
        · rcases ih low' high' L' (by omega) hP' hle' with
            ⟨low'', high'', L'', hw, heq', hP''⟩ | hw
          · exact Or.inl ⟨low'', high'', L'',
              ExecStmt.whileTrue (htrue low high L hP heq) hb hw, heq', hP''⟩
          · exact Or.inr (ExecStmt.whileTrue (htrue low high L hP heq) hb hw)
  exact key (high - low) low high L le_rfl hP hle

/-- The body executes to `.reverted` whenever the `price ≤ 1e18` guard fails. -/
theorem p2tBodyStele_req (cfg : Config) (caller : Frame) (evm : EVM.State)
    (p : Nat) (hp : ¬ p ≤ 1000000000000000000)
    (hloc : caller.locals.get? "price" = some (.int (Int.ofNat p))) :
    ExecFuncBody cfg caller evm priceToTickBodyDecl.body .reverted := by
  rw [p2tBodyDecl_body_eq]
  have hreq : evalExpr? cfg caller evm
      (.binary .le (.var "price") (.intLit 1000000000000000000)) =
      .ok (.bool false) := by
    simp only [evalExpr?, hloc, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    rw [show decide (Int.ofNat p ≤ (1000000000000000000 : Int)) = false from
      decide_eq_false_iff_not.mpr (by
        intro hc
        exact hp (Int.ofNat_le.mp hc))]
  exact ExecFuncBody.execBlockRevert (ABlock.start.requireRevert hreq)

/-- `inRange uint256T` on a value already known to be in range. -/
theorem p2tInRange_ok {cfg : Config} {F : Frame} {evm : EVM.State} {e : Expr} {i : Int}
    (he : evalExpr? cfg F evm e = .ok (.int i))
    (h0 : ¬ i < 0) (h1 : ¬ (2 : Int) ^ 256 ≤ i) :
    evalExpr? cfg F evm (.inRange uint256T e) = .ok (.int i) := by
  simp only [evalExpr?, he, EvalResult.bind, bind, pure]
  rw [show (i < (0:Int) || (2:Int)^256 ≤ i) = false from by
    rw [show decide (i < (0:Int)) = false from decide_eq_false_iff_not.mpr h0,
        show decide ((2:Int)^256 ≤ i) = false from decide_eq_false_iff_not.mpr h1]
    rfl]
  exact if_neg (by decide)

/-- `inRange uint256T` reverts on an out-of-range value. -/
theorem p2tInRange_rev {cfg : Config} {F : Frame} {evm : EVM.State} {e : Expr} {i : Int}
    (he : evalExpr? cfg F evm e = .ok (.int i))
    (h : i < 0 ∨ (2 : Int) ^ 256 ≤ i) :
    evalExpr? cfg F evm (.inRange uint256T e) = .revert := by
  simp only [evalExpr?, he, EvalResult.bind, bind, pure]
  have hc : (i < (0:Int) || (2:Int)^256 ≤ i) = true := by
    rcases h with h0 | h1
    · rw [decide_eq_true_iff.mpr h0]
      rfl
    · by_cases h0 : i < 0
      · rw [decide_eq_true_iff.mpr h0]
        rfl
      · rw [show decide (i < (0:Int)) = false from decide_eq_false_iff_not.mpr h0,
            decide_eq_true_iff.mpr h1]
        rfl
  rw [hc]
  rfl

/-- The loop-coupled Stele evaluation: the `while` either completes to the post-loop locals
    (`low = high`) or reverts mid-iteration when an internal `tickToPrice_body` call reverts.
    Proof is a coupled induction on `high - low` mirroring `execWhile_var`/`whileRevert`. -/
theorem p2tBodyStele (cfg : Config) (caller : Frame) (evm : EVM.State)
    (p s : Nat) (hp : p ≤ 1000000000000000000)
    (hcontract : caller.contract = contract)
    (hlp : caller.locals.get? "price" = some (.int (Int.ofNat p)))
    (hls : caller.locals.get? "spacing" = some (.int (Int.ofNat s))) :
    (∃ (stele' : Frame) (low : Nat), ExecFuncBody cfg caller evm priceToTickBodyDecl.body
        (.returned stele' evm (some [.int (pttResult low (Int.ofNat s))])) ∧
      low ≤ 6744 ∧ low + Int.ofNat s < Int.ofNat EVM.wordModulus ∧ 1 ≤ low + Int.ofNat s ∧
      Int.ofNat s ≠ 0) ∨
    (ExecFuncBody cfg caller evm priceToTickBodyDecl.body .reverted) := by
  rw [p2tBodyDecl_body_eq]
  have hreq : evalExpr? cfg caller evm
      (.binary .le (.var "price") (.intLit 1000000000000000000)) = .ok (.bool true) := by
    simp only [evalExpr?, hlp, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    rw [show decide (Int.ofNat p ≤ (1000000000000000000 : Int)) = true from
      decide_eq_true_iff.mpr (Int.ofNat_le.mpr hp)]
  have hlowEval : evalExpr? cfg caller evm (.intLit 0) = .ok (.int 0) := by
    simp only [evalExpr?, pure]
  have hhighEval : evalExpr? cfg
      { caller with locals := caller.locals.insert "low" (.int 0) } evm (.intLit 6744) =
      .ok (.int 6744) := by
    simp only [evalExpr?, pure]
  -- The loop invariant on the post-init locals.
  let P : ℕ → ℕ → Store → Prop := fun low high L =>
    L.get? "low" = some (.int (Int.ofNat low)) ∧
    L.get? "high" = some (.int (Int.ofNat high)) ∧
    L.get? "price" = some (.int (Int.ofNat p)) ∧
    L.get? "spacing" = some (.int (Int.ofNat s)) ∧
    low ≤ high ∧ high ≤ 6744
  have hP0 : P 0 6744 ((caller.locals.insert "low" (.int 0)).insert "high" (.int 6744)) := by
    refine ⟨?_, ?_, ?_, ?_, by omega, by omega⟩
    · rw [store_get_ne _ (.int 6744) (by decide : ("high" == "low") = false)]
      exact store_get_self _ _ _
    · exact store_get_self _ _ _
    · rw [store_get_ne _ (.int 6744) (by decide : ("high" == "price") = false),
        store_get_ne _ (.int 0) (by decide : ("low" == "price") = false)]
      exact hlp
    · rw [store_get_ne _ (.int 6744) (by decide : ("high" == "spacing") = false),
        store_get_ne _ (.int 0) (by decide : ("low" == "spacing") = false)]
      exact hls
  have hfalse : ∀ low high L, P low high L → low = high →
      evalExpr? cfg { caller with locals := L } evm
        (.binary .ne (.var "low") (.var "high")) = .ok (.bool false) := by
    intro low high L hP heq
    obtain ⟨hl, hh, _, _, _, _⟩ := hP
    simp only [evalExpr?, hl, hh, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    have hb : (decide ((Value.int (Int.ofNat low)) = (Value.int (Int.ofNat high)))) =
        true :=
      decide_eq_true_iff.mpr (congrArg Value.int (congrArg Int.ofNat heq))
    show EvalResult.ok (Value.bool (!(decide
        ((Value.int (Int.ofNat low)) = (Value.int (Int.ofNat high)))))) =
      EvalResult.ok (Value.bool false)
    rw [hb]
    rfl
  have htrue : ∀ low high L, P low high L → low ≠ high →
      evalExpr? cfg { caller with locals := L } evm
        (.binary .ne (.var "low") (.var "high")) = .ok (.bool true) := by
    intro low high L hP hne
    obtain ⟨hl, hh, _, _, _, _⟩ := hP
    simp only [evalExpr?, hl, hh, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    have hb : (decide ((Value.int (Int.ofNat low)) = (Value.int (Int.ofNat high)))) =
        false :=
      decide_eq_false_iff_not.mpr (fun hc =>
        hne (Int.ofNat_inj.mp (by injection hc)))
    show EvalResult.ok (Value.bool (!(decide
        ((Value.int (Int.ofNat low)) = (Value.int (Int.ofNat high)))))) =
      EvalResult.ok (Value.bool true)
    rw [hb]
    rfl
  have hstep : ∀ low high L, P low high L → low < high →
      ExecBlock cfg { caller with locals := L } evm
        [.letDecl "mid" none
          (.binary .div
            (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)),
         .internalCall "tickToPrice_body" [.var "mid"] "__c0",
         .ite (.binary .lt (.var "__c0") (.var "price"))
           [.assign .localVar { base := "low", steps := [] }
             (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
           [.assign .localVar { base := "high", steps := [] } (.var "mid")]] .reverted ∨
      ∃ low' high' L', ExecBlock cfg { caller with locals := L } evm
        [.letDecl "mid" none
          (.binary .div
            (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)),
         .internalCall "tickToPrice_body" [.var "mid"] "__c0",
         .ite (.binary .lt (.var "__c0") (.var "price"))
           [.assign .localVar { base := "low", steps := [] }
             (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
           [.assign .localVar { base := "high", steps := [] } (.var "mid")]]
          (.ok { caller with locals := L' } evm) ∧
        P low' high' L' ∧ low' ≤ high' ∧ high' - low' < high - low := by
    intro low high L hP hlt
    obtain ⟨hlow, hhigh, hprice, hsp, hle, hh6744⟩ := hP
    set mid : Nat := (low + high) / 2 with hmid_def
    have hmidlt : mid < high := by omega
    have hmidle : low ≤ mid := by omega
    have hadd : evalExpr? cfg { caller with locals := L } evm
        (.binary .add (.var "low") (.var "high")) = .ok (.int (Int.ofNat low + Int.ofNat high)) := by
      simp only [evalExpr?, hlow, hhigh, evalBinaryOp?, EvalResult.bind, bind,
        EvalResult.ofOption]
    have hcast : evalExpr? cfg { caller with locals := L } evm
        (.cast (.binary .add (.var "low") (.var "high")) uint256S) =
        .ok (.int (Int.ofNat low + Int.ofNat high)) := by
      simp only [evalExpr?, hadd, EvalResult.bind, bind, EvalResult.ofOption, castValue_int]
      have hW : (EVM.twoPow 256 : Nat) = 2 ^ 256 := rfl
      rw [normalizeInt_uint_eq_self _ _ (by
          have h0 : (0 : Int) ≤ Int.ofNat low := Int.ofNat_nonneg _
          have h1 : (0 : Int) ≤ Int.ofNat high := Int.ofNat_nonneg _
          omega) (by
        rw [hW]
        rw [show Int.ofNat low + Int.ofNat high = Int.ofNat (low + high) from by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
        exact Int.ofNat_lt.mpr (by omega))]
    have hdiv : evalExpr? cfg { caller with locals := L } evm
        (.binary .div
          (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)) =
        .ok (.int (Int.ofNat mid)) := by
      have hmidI : (Int.ofNat low + Int.ofNat high) / (2 : Int) = Int.ofNat mid := by
        rw [hmid_def]
        rw [show Int.ofNat low + Int.ofNat high = Int.ofNat (low + high) from by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
        show Int.ofNat (low + high) / Int.ofNat 2 = Int.ofNat ((low + high) / 2)
        simp only [Int.ofNat_eq_natCast]
        rw [Int.ofNat_ediv_ofNat]
      simpa [evalExpr?, hcast, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption,
        hmidI]
    -- internal call `tickToPrice_body(mid)`
    set Lmid := L.insert "mid" (.int (Int.ofNat mid)) with hLmid
    have hmidL : Lmid.get? "mid" = some (.int (Int.ofNat mid)) := store_get_self _ _ _
    have hargs : evalExprs? cfg { caller with locals := Lmid } evm [.var "mid"] =
        .ok [.int (Int.ofNat mid)] :=
      evalExprs?_singleton (by simp only [evalExpr?, hmidL, EvalResult.ofOption])
    have hlookup : lookupCallable? ({ caller with locals := Lmid }).contract
        "tickToPrice_body" = some tickToPriceBodyDecl.toCallable := by
      show lookupCallable? caller.contract "tickToPrice_body" = _
      rw [hcontract]
      rfl
    have hbind : bindParams? tickToPriceBodyDecl.params [.int (Int.ofNat mid)] =
        some ((∅ : Store).insert "tick" (.int (Int.ofNat mid))) := rfl
    by_cases hdz0 : ttpArg mid < 0 ∧ wExpPos (-ttpArg mid) = 0
    · -- inner `wExp_body` divisor is zero: the internal call reverts.
      left
      have hrev := t2pBodyStele_divZero cfg
        { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
        evm mid (by omega) hcontract (store_get_self _ _ _) hdz0.1 hdz0.2
      have hic := internalCallFunctionRevert (name := "tickToPrice_body") (retVar := "__c0")
        (args := [.var "mid"]) (argVals := [.int (Int.ofNat mid)])
        (callee := tickToPriceBodyDecl)
        (locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)))
        hargs hlookup hbind hrev
      exact ExecBlock.consNormal (ExecStmt.letDecl hdiv) (ExecBlock.consRevert hic)
    · by_cases hdz : ttpDen (wExpVal (ttpArg mid)) = 0
      · -- inner `__d1` denominator is zero: the internal call reverts.
        left
        have hrev := t2pBodyStele_denZero cfg
          { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
          evm mid (by omega) hcontract (store_get_self _ _ _)
          (fun hneg hz => hdz0 ⟨hneg, hz⟩) hdz
        have hic := internalCallFunctionRevert (name := "tickToPrice_body")
          (retVar := "__c0") (args := [.var "mid"]) (argVals := [.int (Int.ofNat mid)])
          (callee := tickToPriceBodyDecl)
          (locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)))
          hargs hlookup hbind hrev
        exact ExecBlock.consNormal (ExecStmt.letDecl hdiv) (ExecBlock.consRevert hic)
      · -- ordinary iteration: `__c0 = ttpResult mid`, then the `ite` update.
        obtain ⟨stele', hbody⟩ := t2pBodyStele cfg
          { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
          evm mid (by omega) hcontract (store_get_self _ _ _)
          (fun hneg hz => hdz0 ⟨hneg, hz⟩) hdz
        have hic := internalCallFunctionReturn (name := "tickToPrice_body")
          (retVar := "__c0") (args := [.var "mid"]) (argVals := [.int (Int.ofNat mid)])
          (callee := tickToPriceBodyDecl)
          (locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)))
          hargs hlookup hbind hbody
        set Lres := Lmid.insert "__c0" (.int (ttpResult mid)) with hLres
        have hc0 : Lres.get? "__c0" = some (.int (ttpResult mid)) :=
          store_get_self _ _ _
        have hprice' : Lres.get? "price" = some (.int (Int.ofNat p)) := by
          rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "price") = false),
            hLmid, store_get_ne _ _ (by decide : ("mid" == "price") = false)]
          exact hprice
        have hmidL' : Lres.get? "mid" = some (.int (Int.ofNat mid)) := by
          rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "mid") = false)]
          exact store_get_self _ _ _
        have hlowL' : Lres.get? "low" = some (.int (Int.ofNat low)) := by
          rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "low") = false),
            hLmid, store_get_ne _ _ (by decide : ("mid" == "low") = false)]
          exact hlow
        have hhighL' : Lres.get? "high" = some (.int (Int.ofNat high)) := by
          rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "high") = false),
            hLmid, store_get_ne _ _ (by decide : ("mid" == "high") = false)]
          exact hhigh
        have hspL' : Lres.get? "spacing" = some (.int (Int.ofNat s)) := by
          rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "spacing") = false),
            hLmid, store_get_ne _ _ (by decide : ("mid" == "spacing") = false)]
          exact hsp
        have hcond : evalExpr? cfg { caller with locals := Lres } evm
            (.binary .lt (.var "__c0") (.var "price")) =
            .ok (.bool (decide (ttpResult mid < Int.ofNat p))) := by
          simp only [evalExpr?, hc0, hprice', evalBinaryOp?, EvalResult.bind, bind,
            EvalResult.ofOption]
        by_cases hltc : ttpResult mid < Int.ofNat p
        · -- `low := uint256(mid + 1)`
          have hcondT : evalExpr? cfg { caller with locals := Lres } evm
              (.binary .lt (.var "__c0") (.var "price")) = .ok (.bool true) := by
            rw [hcond,
              show decide (ttpResult mid < Int.ofNat p) = true from
                decide_eq_true_iff.mpr hltc]
          have hplus1 : evalExpr? cfg { caller with locals := Lres } evm
              (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S) =
              .ok (.int (Int.ofNat mid + 1)) := by
            have he0 : evalExpr? cfg { caller with locals := Lres } evm
                (.binary .add (.var "mid") (.intLit 1)) = .ok (.int (Int.ofNat mid + 1)) := by
              simp only [evalExpr?, hmidL', evalBinaryOp?, EvalResult.bind, bind,
                EvalResult.ofOption]
            simp only [evalExpr?, he0, EvalResult.bind, bind, EvalResult.ofOption,
              castValue_int]
            have hW : (EVM.twoPow 256 : Nat) = 2 ^ 256 := rfl
            rw [normalizeInt_uint_eq_self _ _ (by
                have h0 : (0 : Int) ≤ Int.ofNat mid := Int.ofNat_nonneg _
                omega) (by
              rw [hW]
              rw [show Int.ofNat mid + 1 = Int.ofNat (mid + 1) from by
                simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]]
              exact Int.ofNat_lt.mpr (by omega))]
          have hass := ExecStmt.assign (Or.inl rfl) hplus1 (assignLocalBase_ok hlowL')
          have hite : ExecStmt cfg { caller with locals := Lres } evm
              (.ite (.binary .lt (.var "__c0") (.var "price"))
                [.assign .localVar { base := "low", steps := [] }
                  (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
                [.assign .localVar { base := "high", steps := [] } (.var "mid")])
              (.ok ⟨caller.contract, Lres.insert "low" (.int (Int.ofNat mid + 1)),
                  caller.immutables⟩ evm) :=
            ExecStmt.iteTrue hcondT (ExecBlock.consNormal hass ExecBlock.nil)
          refine Or.inr ⟨mid + 1, high, Lres.insert "low" (.int (Int.ofNat mid + 1)),
            ExecBlock.consNormal (ExecStmt.letDecl hdiv)
              (ExecBlock.consNormal hic (ExecBlock.consNormal hite ExecBlock.nil)),
            ?_, by omega, by omega⟩
          refine ⟨?_, ?_, ?_, ?_, by omega, hh6744⟩
          · exact store_get_self _ _ _
          · rw [store_get_ne _ _ (by decide : ("low" == "high") = false)]
            exact hhighL'
          · rw [store_get_ne _ _ (by decide : ("low" == "price") = false)]
            exact hprice'
          · rw [store_get_ne _ _ (by decide : ("low" == "spacing") = false)]
            exact hspL'
        · -- `high := mid`
          have hcondF : evalExpr? cfg { caller with locals := Lres } evm
              (.binary .lt (.var "__c0") (.var "price")) = .ok (.bool false) := by
            rw [hcond,
              show decide (ttpResult mid < Int.ofNat p) = false from
                decide_eq_false_iff_not.mpr hltc]
          have hmidE : evalExpr? cfg { caller with locals := Lres } evm (.var "mid") =
              .ok (.int (Int.ofNat mid)) := by
            simp only [evalExpr?, hmidL', EvalResult.ofOption]
          have hass := ExecStmt.assign (Or.inl rfl) hmidE (assignLocalBase_ok hhighL')
          have hite : ExecStmt cfg { caller with locals := Lres } evm
              (.ite (.binary .lt (.var "__c0") (.var "price"))
                [.assign .localVar { base := "low", steps := [] }
                  (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
                [.assign .localVar { base := "high", steps := [] } (.var "mid")])
              (.ok ⟨caller.contract, Lres.insert "high" (.int (Int.ofNat mid)),
                  caller.immutables⟩ evm) :=
            ExecStmt.iteFalse hcondF (ExecBlock.consNormal hass ExecBlock.nil)
          refine Or.inr ⟨low, mid, Lres.insert "high" (.int (Int.ofNat mid)),
            ExecBlock.consNormal (ExecStmt.letDecl hdiv)
              (ExecBlock.consNormal hic (ExecBlock.consNormal hite ExecBlock.nil)),
            ?_, hmidle, by omega⟩
          refine ⟨?_, ?_, ?_, ?_, hmidle, by omega⟩
          · rw [store_get_ne _ _ (by decide : ("high" == "low") = false)]
            exact hlowL'
          · exact store_get_self _ _ _
          · rw [store_get_ne _ _ (by decide : ("high" == "price") = false)]
            exact hprice'
          · rw [store_get_ne _ _ (by decide : ("high" == "spacing") = false)]
            exact hspL'
  have hchain := (ABlock.start.requireStep hreq).letStep (ty := none) hlowEval |>.letStep
    (name := "high") (ty := none) (rest :=
      [.while (.binary .ne (.var "low") (.var "high"))
        [.letDecl "mid" none
          (.binary .div
            (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)),
         .internalCall "tickToPrice_body" [.var "mid"] "__c0",
         .ite (.binary .lt (.var "__c0") (.var "price"))
           [.assign .localVar { base := "low", steps := [] }
             (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
           [.assign .localVar { base := "high", steps := [] } (.var "mid")]],
       .return [.binary .mul
         (.inRange uint256T
           (.binary .div
             (.inRange uint256T
               (.binary .sub
                 (.inRange uint256T
                   (.binary .add (.var "low") (.var "spacing")))
                 (.intLit 1)))
             (.var "spacing")))
         (.var "spacing")]]) hhighEval
  rcases execWhile_revert P hfalse htrue hstep 0 6744
      ((caller.locals.insert "low" (.int 0)).insert "high" (.int 6744)) hP0 (by omega) with
    ⟨low', high', L', hwhile, heq, hP'⟩ | hwhile
  · subst heq
    obtain ⟨hlow', hhigh', hprice', hsp', hle', hh'⟩ := hP'
    have hWM : (Int.ofNat EVM.wordModulus : Int) = (2 : Int) ^ 256 := by decide
    have hl'nn : (0 : Int) ≤ Int.ofNat low' := Int.ofNat_nonneg _
    have hsnn : (0 : Int) ≤ Int.ofNat s := Int.ofNat_nonneg _
    -- exit tail: `((low + spacing) as u - 1) as u / spacing) as u * spacing`
    have haddE : evalExpr? cfg { caller with locals := L' } evm
        (.binary .add (.var "low") (.var "spacing")) =
        .ok (.int (Int.ofNat low' + Int.ofNat s)) := by
      simp only [evalExpr?, hlow', hsp', evalBinaryOp?, EvalResult.bind, bind,
        EvalResult.ofOption]
    by_cases hov : Int.ofNat EVM.wordModulus ≤ Int.ofNat low' + Int.ofNat s
    · -- `(low + spacing) as uint256` overflows → revert
      right
      have hR1 : evalExpr? cfg { caller with locals := L' } evm
          (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) = .revert :=
        p2tInRange_rev haddE (Or.inr (hWM ▸ hov))
      have hmulR : evalExpr? cfg { caller with locals := L' } evm
          (.binary .mul
            (.inRange uint256T
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T
                      (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")))
            (.var "spacing")) = .revert := by
        simp only [evalExpr?, hR1, EvalResult.bind, bind]
      have hret : evalExprs? cfg { caller with locals := L' } evm
          [.binary .mul
            (.inRange uint256T
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T
                      (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")))
            (.var "spacing")] = .revert := by
        simp only [evalExprs?, hmulR, EvalResult.bind, bind]
      exact ExecFuncBody.execBlockRevert (hchain |>.run
        (ExecBlock.consNormal hwhile (ExecBlock.consRevert (ExecStmt.returnRevert hret))))
    · by_cases hzero : Int.ofNat low' + Int.ofNat s < 1
      · -- `low + spacing - 1 < 0`: the second `as uint256` reverts.
        right
        have hR1 : evalExpr? cfg { caller with locals := L' } evm
            (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) =
            .ok (.int (Int.ofNat low' + Int.ofNat s)) :=
          p2tInRange_ok haddE (by omega) (by omega)
        have hsubE : evalExpr? cfg { caller with locals := L' } evm
            (.binary .sub
              (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
              (.intLit 1)) = .ok (.int (Int.ofNat low' + Int.ofNat s - 1)) := by
          simp only [evalExpr?, hR1, evalBinaryOp?, EvalResult.bind, bind,
            EvalResult.ofOption]
        have hR2 : evalExpr? cfg { caller with locals := L' } evm
            (.inRange uint256T
              (.binary .sub
                (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                (.intLit 1))) = .revert :=
          p2tInRange_rev hsubE (Or.inl (by omega))
        have hmulR : evalExpr? cfg { caller with locals := L' } evm
            (.binary .mul
              (.inRange uint256T
                (.binary .div
                  (.inRange uint256T
                    (.binary .sub
                      (.inRange uint256T
                        (.binary .add (.var "low") (.var "spacing")))
                      (.intLit 1)))
                  (.var "spacing")))
              (.var "spacing")) = .revert := by
          simp only [evalExpr?, hR2, EvalResult.bind, bind]
        have hret : evalExprs? cfg { caller with locals := L' } evm
            [.binary .mul
              (.inRange uint256T
                (.binary .div
                  (.inRange uint256T
                    (.binary .sub
                      (.inRange uint256T
                        (.binary .add (.var "low") (.var "spacing")))
                      (.intLit 1)))
                  (.var "spacing")))
              (.var "spacing")] = .revert := by
          simp only [evalExprs?, hmulR, EvalResult.bind, bind]
        exact ExecFuncBody.execBlockRevert (hchain |>.run
          (ExecBlock.consNormal hwhile (ExecBlock.consRevert (ExecStmt.returnRevert hret))))
      · by_cases hs0 : Int.ofNat s = 0
        · -- `spacing = 0`: the `/` reverts.
          right
          have hR1 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) =
              .ok (.int (Int.ofNat low' + Int.ofNat s)) :=
            p2tInRange_ok haddE (by omega) (by omega)
          have hsubE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .sub
                (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                (.intLit 1)) = .ok (.int (Int.ofNat low' + Int.ofNat s - 1)) := by
            simp only [evalExpr?, hR1, evalBinaryOp?, EvalResult.bind, bind,
              EvalResult.ofOption]
          have hR2 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T
                (.binary .sub
                  (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                  (.intLit 1))) = .ok (.int (Int.ofNat low' + Int.ofNat s - 1)) :=
            p2tInRange_ok hsubE (by omega) (by omega)
          have hspE : evalExpr? cfg { caller with locals := L' } evm (.var "spacing") =
              .ok (.int (Int.ofNat s)) := by
            simp only [evalExpr?, hsp', EvalResult.ofOption]
          have hdivR : evalExpr? cfg { caller with locals := L' } evm
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")) = .revert := by
            simp only [evalExpr?, hR2, hspE, evalBinaryOp?, EvalResult.bind, bind,
              hs0]
            rfl
          have hmulR : evalExpr? cfg { caller with locals := L' } evm
              (.binary .mul
                (.inRange uint256T
                  (.binary .div
                    (.inRange uint256T
                      (.binary .sub
                        (.inRange uint256T
                          (.binary .add (.var "low") (.var "spacing")))
                        (.intLit 1)))
                    (.var "spacing")))
                (.var "spacing")) = .revert := by
            simp only [evalExpr?, hdivR, EvalResult.bind, bind]
          have hret : evalExprs? cfg { caller with locals := L' } evm
              [.binary .mul
                (.inRange uint256T
                  (.binary .div
                    (.inRange uint256T
                      (.binary .sub
                        (.inRange uint256T
                          (.binary .add (.var "low") (.var "spacing")))
                        (.intLit 1)))
                    (.var "spacing")))
                (.var "spacing")] = .revert := by
            simp only [evalExprs?, hmulR, EvalResult.bind, bind]
          exact ExecFuncBody.execBlockRevert (hchain |>.run
            (ExecBlock.consNormal hwhile
              (ExecBlock.consRevert (ExecStmt.returnRevert hret))))
        · -- all guards pass: return `(low + spacing - 1) / spacing * spacing`.
          left
          have hR1 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) =
              .ok (.int (Int.ofNat low' + Int.ofNat s)) :=
            p2tInRange_ok haddE (by omega) (by omega)
          have hsubE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .sub
                (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                (.intLit 1)) = .ok (.int (Int.ofNat low' + Int.ofNat s - 1)) := by
            simp only [evalExpr?, hR1, evalBinaryOp?, EvalResult.bind, bind,
              EvalResult.ofOption]
          have hR2 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T
                (.binary .sub
                  (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                  (.intLit 1))) = .ok (.int (Int.ofNat low' + Int.ofNat s - 1)) :=
            p2tInRange_ok hsubE (by omega) (by omega)
          have hspE : evalExpr? cfg { caller with locals := L' } evm (.var "spacing") =
              .ok (.int (Int.ofNat s)) := by
            simp only [evalExpr?, hsp', EvalResult.ofOption]
          have hdivE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")) = .ok (.int ((Int.ofNat low' + Int.ofNat s - 1)
                  / Int.ofNat s)) := by
            simp only [evalExpr?, hR2, hspE, evalBinaryOp?, EvalResult.bind, bind, hs0]
            rfl
          have hR3 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T
                (.binary .div
                  (.inRange uint256T
                    (.binary .sub
                      (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                      (.intLit 1)))
                  (.var "spacing"))) =
              .ok (.int ((Int.ofNat low' + Int.ofNat s - 1) / Int.ofNat s)) := by
            have hnn : 0 ≤ Int.ofNat low' + Int.ofNat s - 1 := by omega
            have hnn2 : 0 ≤ (Int.ofNat low' + Int.ofNat s - 1) / Int.ofNat s :=
              Int.ediv_nonneg hnn hsnn
            have hle2 : (Int.ofNat low' + Int.ofNat s - 1) / Int.ofNat s ≤
                Int.ofNat low' + Int.ofNat s - 1 := Int.ediv_le_self _ hnn
            exact p2tInRange_ok hdivE (by omega) (by omega)
          have hmulE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .mul
                (.inRange uint256T
                  (.binary .div
                    (.inRange uint256T
                      (.binary .sub
                        (.inRange uint256T
                          (.binary .add (.var "low") (.var "spacing")))
                        (.intLit 1)))
                    (.var "spacing")))
                (.var "spacing")) =
              .ok (.int (pttResult (Int.ofNat low') (Int.ofNat s))) := by
            simp only [evalExpr?, hR3, hspE, evalBinaryOp?, EvalResult.bind, bind,
              pttResult]
          refine ⟨{ caller with locals := L' }, low',
            ExecFuncBody.execBlockRet ((hchain).whileStep hwhile |>.returns hmulE),
            by omega, ?_, ?_, hs0⟩
          · show Int.ofNat low' + Int.ofNat s < Int.ofNat EVM.wordModulus
            omega
          · show (1 : Int) ≤ Int.ofNat low' + Int.ofNat s
            omega
  · exact Or.inr (ExecFuncBody.execBlockRevert (hchain |>.run
      (ExecBlock.consRevert hwhile)))

/-! ## EVM-side traces -/

/-- Nonpayable calls take the `callvalue`-guard revert branch (pc 168 → 131). -/
theorem p2tX_revert_pay {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 3)) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachPriceToTickBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_168_taken (by simp) hwv
    (by jump_dest) rd
  exact tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd1

/-- Calldata shorter than `4 + 64` reverts via the `174 → 131` size guard. -/
theorem p2tX_rev {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 3)) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachPriceToTickBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_168_fallthrough (by simp) hwv rd
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨64⟩ ≠
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 64) ≠ ⟨0⟩
    rcases hshort with hs | hb
    · rw [slt_ofNat_lit_one_low (by norm_num) (by omega : I.calldata.size - 4 < 64)]
      decide
    · rw [slt_lit_one_high (a := UInt256.ofNat (I.calldata.size - 4)) (m := 64)
        (by norm_num) (by rw [ulit_toNat' _ (by omega : I.calldata.size - 4 <
          UInt256.size)]; omega)]
      decide
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_174_taken (by simp) hslt
    (by jump_dest) rd1
  exact tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd2

/-- `price > 1e18`: the `186` gate takes the panic revert at `344`. -/
theorem p2tX_rev_gate {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (h68 : 68 ≤ I.calldata.size)
    (hsel : selIs I (tickLibWrapperSelBytes 3))
    (hgt : 1000000000000000000 < (calldataWord I.calldata 4).toNat) :
    RDrev tickLibWrapperBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachPriceToTickBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_168_fallthrough (by simp) hwv rd
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨64⟩ =
      ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 64) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_174_fallthrough (by simp) hslt rd1
  have hgt' : UInt256.gt (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32))
      (UInt256.ofNat 1000000000000000000) ≠ ⟨0⟩ := by
    have h1 : UInt256.gt (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32))
        (UInt256.ofNat 1000000000000000000) = ⟨1⟩ := by
      apply ugt_one
      rw [ulit_toNat' _ (by decide : (1000000000000000000 : Nat) < UInt256.size)]
      have hw : (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toNat =
          (calldataWord I.calldata 4).toNat := rfl
      rw [hw]
      exact hgt
    rw [h1]; decide
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_186_taken (by simp) hgt'
    (by jump_dest) rd2
  exact tickLibWrapperBlocks.tickLibWrapper_block_344
    (by simp only [tickLibWrapperBlocks.tickLibWrapper_block_186_taken_stack,
      List.length_cons, List.length_nil]; omega) rd3

/-- Coupled `while`/`RD` induction for the binary-search loop: at variant `v` the loop either
    exits to `221` with `low = high`, reverts both sides inside an iteration, or takes one
    step to the next variant.  The EVM memory/active-words/account map are loop-invariant;
    only the stack `[price, high, low, spacing] ++ R` changes. -/
theorem p2tLoopOrRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : AccountMap} {α : Type}
    {evm : EVM.State}
    (R : List UInt256) (mem : ByteArray) (aw : UInt256)
    (Inv : ℕ → α → Store → Prop) (stk : α → List UInt256)
    (exitStk : α → List UInt256) {cfg : Config} {contract : ContractDecl} {imms : Store}
    {condExpr : Expr} {body : List Stmt}
    (hfalse : ∀ a L, Inv 0 a L →
      evalExpr? cfg { contract := contract, locals := L, immutables := imms } evm condExpr =
        .ok (.bool false))
    (hexit : ∀ a L, Inv 0 a L → ∀ k C,
      RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213) (stk a) mem aw rdata acc k C →
      ∃ k' C', RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 221) (exitStk a)
        mem aw rdata acc k' C')
    (htrue : ∀ v a L, Inv (v + 1) a L →
      evalExpr? cfg { contract := contract, locals := L, immutables := imms } evm condExpr =
        .ok (.bool true))
    (hbody : ∀ v a L, Inv (v + 1) a L → ∀ k C,
      RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213) (stk a) mem aw rdata acc k C →
      (ExecBlock cfg { contract := contract, locals := L, immutables := imms } evm body
          .reverted ∧ RDrev tickLibWrapperBytecode g s0) ∨
      ∃ a' L' k' C', ExecBlock cfg { contract := contract, locals := L, immutables := imms }
          evm body (.ok { contract := contract, locals := L', immutables := imms } evm) ∧
        Inv v a' L' ∧
        RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213) (stk a') mem aw rdata acc k' C') :
    ∀ v a L, Inv v a L → ∀ k C,
      RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213) (stk a) mem aw rdata acc k C →
      (∃ a' L' k' C',
        ExecStmt cfg { contract := contract, locals := L, immutables := imms } evm
          (.while condExpr body)
          (.ok { contract := contract, locals := L', immutables := imms } evm) ∧
        Inv 0 a' L' ∧
        RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 221) (exitStk a')
          mem aw rdata acc k' C') ∨
      (ExecStmt cfg { contract := contract, locals := L, immutables := imms } evm
          (.while condExpr body) .reverted ∧
        RDrev tickLibWrapperBytecode g s0) := by
  intro v
  induction v with
  | zero =>
    intro a L hInv k C rd
    obtain ⟨k', C', rdExit⟩ := hexit a L hInv k C rd
    exact Or.inl ⟨a, L, k', C', ExecStmt.whileFalse (hfalse a L hInv), hInv, rdExit⟩
  | succ v ih =>
    intro a L hInv k C rd
    rcases hbody v a L hInv k C rd with hrev | hstep
    · exact Or.inr ⟨ExecStmt.whileRevert (htrue v a L hInv) hrev.1, hrev.2⟩
    · obtain ⟨a', L', k', C', hblock, hInv', rdNext⟩ := hstep
      rcases ih a' L' hInv' k' C' rdNext with hdone | hloopRev
      · rcases hdone with ⟨a'', L'', k2, C2, hloop, hInv0, rdExit⟩
        exact Or.inl ⟨a'', L'', k2, C2,
          ExecStmt.whileTrue (htrue v a L hInv) hblock hloop, hInv0, rdExit⟩
      · rcases hloopRev with ⟨hloop, hrdRev⟩
        exact Or.inr ⟨ExecStmt.whileTrue (htrue v a L hInv) hblock hloop, hrdRev⟩

/-! ### Spec-side single-iteration lemmas

Standalone forms of the loop-body step inside `p2tBodyStele`, split so the caller can
decide the revert (`wExp` divisor zero / denominator zero) versus success branch before
invoking them — needed for the coupled EVM/Stele loop `p2tX_loop`. -/

/-- One loop-body pass reverts when an inner `tickToPrice_body(mid)` evaluation reverts. -/
theorem p2tStep_rev (cfg : Config) (caller : Frame) (evm : EVM.State)
    (low high : Nat) (L : Store)
    (hcontract : caller.contract = contract)
    (hlow : L.get? "low" = some (.int (Int.ofNat low)))
    (hhigh : L.get? "high" = some (.int (Int.ofNat high)))
    (hle : low ≤ high) (hh6744 : high ≤ 6744) (hlt : low < high)
    (hrev0 : (ttpArg ((low + high) / 2) < 0 ∧
        wExpPos (-ttpArg ((low + high) / 2)) = 0) ∨
      ttpDen (wExpVal (ttpArg ((low + high) / 2))) = 0) :
    ExecBlock cfg { caller with locals := L } evm
      [.letDecl "mid" none
        (.binary .div
          (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)),
       .internalCall "tickToPrice_body" [.var "mid"] "__c0",
       .ite (.binary .lt (.var "__c0") (.var "price"))
         [.assign .localVar { base := "low", steps := [] }
           (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
         [.assign .localVar { base := "high", steps := [] } (.var "mid")]] .reverted := by
  set mid : Nat := (low + high) / 2 with hmid_def
  have hmidlt : mid < high := by omega
  have hadd : evalExpr? cfg { caller with locals := L } evm
      (.binary .add (.var "low") (.var "high")) = .ok (.int (Int.ofNat low + Int.ofNat high)) := by
    simp only [evalExpr?, hlow, hhigh, evalBinaryOp?, EvalResult.bind, bind,
      EvalResult.ofOption]
  have hcast : evalExpr? cfg { caller with locals := L } evm
      (.cast (.binary .add (.var "low") (.var "high")) uint256S) =
      .ok (.int (Int.ofNat low + Int.ofNat high)) := by
    simp only [evalExpr?, hadd, EvalResult.bind, bind, EvalResult.ofOption, castValue_int]
    have hW : (EVM.twoPow 256 : Nat) = 2 ^ 256 := rfl
    rw [normalizeInt_uint_eq_self _ _ (by
        have h0 : (0 : Int) ≤ Int.ofNat low := Int.ofNat_nonneg _
        have h1 : (0 : Int) ≤ Int.ofNat high := Int.ofNat_nonneg _
        omega) (by
      rw [hW]
      rw [show Int.ofNat low + Int.ofNat high = Int.ofNat (low + high) from by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
      exact Int.ofNat_lt.mpr (by omega))]
  have hdiv : evalExpr? cfg { caller with locals := L } evm
      (.binary .div
        (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)) =
      .ok (.int (Int.ofNat mid)) := by
    have hmidI : (Int.ofNat low + Int.ofNat high) / (2 : Int) = Int.ofNat mid := by
      rw [hmid_def]
      rw [show Int.ofNat low + Int.ofNat high = Int.ofNat (low + high) from by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
      show Int.ofNat (low + high) / Int.ofNat 2 = Int.ofNat ((low + high) / 2)
      simp only [Int.ofNat_eq_natCast]
      rw [Int.ofNat_ediv_ofNat]
    simpa [evalExpr?, hcast, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption,
      hmidI]
  set Lmid := L.insert "mid" (.int (Int.ofNat mid)) with hLmid
  have hmidL : Lmid.get? "mid" = some (.int (Int.ofNat mid)) := store_get_self _ _ _
  have hargs : evalExprs? cfg { caller with locals := Lmid } evm [.var "mid"] =
      .ok [.int (Int.ofNat mid)] :=
    evalExprs?_singleton (by simp only [evalExpr?, hmidL, EvalResult.ofOption])
  have hlookup : lookupCallable? ({ caller with locals := Lmid }).contract
      "tickToPrice_body" = some tickToPriceBodyDecl.toCallable := by
    show lookupCallable? caller.contract "tickToPrice_body" = _
    rw [hcontract]
    rfl
  have hbind : bindParams? tickToPriceBodyDecl.params [.int (Int.ofNat mid)] =
      some ((∅ : Store).insert "tick" (.int (Int.ofNat mid))) := rfl
  have hic_of (hrev : ExecFuncBody cfg
      { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
      evm tickToPriceBodyDecl.body .reverted) :
      ExecBlock cfg { caller with locals := L } evm
        [.letDecl "mid" none
          (.binary .div
            (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)),
         .internalCall "tickToPrice_body" [.var "mid"] "__c0",
         .ite (.binary .lt (.var "__c0") (.var "price"))
           [.assign .localVar { base := "low", steps := [] }
             (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
           [.assign .localVar { base := "high", steps := [] } (.var "mid")]] .reverted :=
    ExecBlock.consNormal (ExecStmt.letDecl hdiv) (ExecBlock.consRevert
      (internalCallFunctionRevert (name := "tickToPrice_body") (retVar := "__c0")
        (args := [.var "mid"]) (argVals := [.int (Int.ofNat mid)])
        (callee := tickToPriceBodyDecl)
        (locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)))
        hargs hlookup hbind hrev))
  rcases hrev0 with hdz0 | hdz
  · exact hic_of (t2pBodyStele_divZero cfg
      { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
      evm mid (by omega) hcontract (store_get_self _ _ _) hdz0.1 hdz0.2)
  · by_cases hdz0' : ttpArg mid < 0 ∧ wExpPos (-ttpArg mid) = 0
    · exact hic_of (t2pBodyStele_divZero cfg
        { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
        evm mid (by omega) hcontract (store_get_self _ _ _) hdz0'.1 hdz0'.2)
    · exact hic_of (t2pBodyStele_denZero cfg
        { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
        evm mid (by omega) hcontract (store_get_self _ _ _)
        (fun hneg hz => hdz0' ⟨hneg, hz⟩) hdz)

/-- One loop-body pass succeeds (inner call returns `ttpResult mid`), updating `low`/`high`
    per the `__c0 < price` comparison. -/
theorem p2tStep_ok (cfg : Config) (caller : Frame) (evm : EVM.State)
    (p s : Nat) (low high : Nat) (L : Store)
    (hcontract : caller.contract = contract)
    (hlow : L.get? "low" = some (.int (Int.ofNat low)))
    (hhigh : L.get? "high" = some (.int (Int.ofNat high)))
    (hprice : L.get? "price" = some (.int (Int.ofNat p)))
    (hsp : L.get? "spacing" = some (.int (Int.ofNat s)))
    (hle : low ≤ high) (hh6744 : high ≤ 6744) (hlt : low < high)
    (hb0 : ¬ (ttpArg ((low + high) / 2) < 0 ∧
        wExpPos (-ttpArg ((low + high) / 2)) = 0))
    (hd : ttpDen (wExpVal (ttpArg ((low + high) / 2))) ≠ 0) :
    ∃ low' high' L',
      ExecBlock cfg { caller with locals := L } evm
        [.letDecl "mid" none
          (.binary .div
            (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)),
         .internalCall "tickToPrice_body" [.var "mid"] "__c0",
         .ite (.binary .lt (.var "__c0") (.var "price"))
           [.assign .localVar { base := "low", steps := [] }
             (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
           [.assign .localVar { base := "high", steps := [] } (.var "mid")]]
        (.ok { caller with locals := L' } evm) ∧
      (L'.get? "low" = some (.int (Int.ofNat low')) ∧
       L'.get? "high" = some (.int (Int.ofNat high')) ∧
       L'.get? "price" = some (.int (Int.ofNat p)) ∧
       L'.get? "spacing" = some (.int (Int.ofNat s)) ∧
       low' ≤ high' ∧ high' ≤ 6744) ∧
      high' - low' < high - low ∧
      (ttpResult ((low + high) / 2) < Int.ofNat p →
        low' = (low + high) / 2 + 1 ∧ high' = high) ∧
      (¬ ttpResult ((low + high) / 2) < Int.ofNat p →
        low' = low ∧ high' = (low + high) / 2) := by
  set mid : Nat := (low + high) / 2 with hmid_def
  have hmidlt : mid < high := by omega
  have hmidle : low ≤ mid := by omega
  have hadd : evalExpr? cfg { caller with locals := L } evm
      (.binary .add (.var "low") (.var "high")) = .ok (.int (Int.ofNat low + Int.ofNat high)) := by
    simp only [evalExpr?, hlow, hhigh, evalBinaryOp?, EvalResult.bind, bind,
      EvalResult.ofOption]
  have hcast : evalExpr? cfg { caller with locals := L } evm
      (.cast (.binary .add (.var "low") (.var "high")) uint256S) =
      .ok (.int (Int.ofNat low + Int.ofNat high)) := by
    simp only [evalExpr?, hadd, EvalResult.bind, bind, EvalResult.ofOption, castValue_int]
    have hW : (EVM.twoPow 256 : Nat) = 2 ^ 256 := rfl
    rw [normalizeInt_uint_eq_self _ _ (by
        have h0 : (0 : Int) ≤ Int.ofNat low := Int.ofNat_nonneg _
        have h1 : (0 : Int) ≤ Int.ofNat high := Int.ofNat_nonneg _
        omega) (by
      rw [hW]
      rw [show Int.ofNat low + Int.ofNat high = Int.ofNat (low + high) from by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
      exact Int.ofNat_lt.mpr (by omega))]
  have hdiv : evalExpr? cfg { caller with locals := L } evm
      (.binary .div
        (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)) =
      .ok (.int (Int.ofNat mid)) := by
    have hmidI : (Int.ofNat low + Int.ofNat high) / (2 : Int) = Int.ofNat mid := by
      rw [hmid_def]
      rw [show Int.ofNat low + Int.ofNat high = Int.ofNat (low + high) from by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
      show Int.ofNat (low + high) / Int.ofNat 2 = Int.ofNat ((low + high) / 2)
      simp only [Int.ofNat_eq_natCast]
      rw [Int.ofNat_ediv_ofNat]
    simpa [evalExpr?, hcast, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption,
      hmidI]
  set Lmid := L.insert "mid" (.int (Int.ofNat mid)) with hLmid
  have hmidL : Lmid.get? "mid" = some (.int (Int.ofNat mid)) := store_get_self _ _ _
  have hargs : evalExprs? cfg { caller with locals := Lmid } evm [.var "mid"] =
      .ok [.int (Int.ofNat mid)] :=
    evalExprs?_singleton (by simp only [evalExpr?, hmidL, EvalResult.ofOption])
  have hlookup : lookupCallable? ({ caller with locals := Lmid }).contract
      "tickToPrice_body" = some tickToPriceBodyDecl.toCallable := by
    show lookupCallable? caller.contract "tickToPrice_body" = _
    rw [hcontract]
    rfl
  have hbind : bindParams? tickToPriceBodyDecl.params [.int (Int.ofNat mid)] =
      some ((∅ : Store).insert "tick" (.int (Int.ofNat mid))) := rfl
  obtain ⟨stele', hbody⟩ := t2pBodyStele cfg
    { caller with locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)) }
    evm mid (by omega) hcontract (store_get_self _ _ _)
    (fun hneg hz => hb0 ⟨hneg, hz⟩) hd
  have hic := internalCallFunctionReturn (name := "tickToPrice_body")
    (retVar := "__c0") (args := [.var "mid"]) (argVals := [.int (Int.ofNat mid)])
    (callee := tickToPriceBodyDecl)
    (locals := (∅ : Store).insert "tick" (.int (Int.ofNat mid)))
    hargs hlookup hbind hbody
  set Lres := Lmid.insert "__c0" (.int (ttpResult mid)) with hLres
  have hc0 : Lres.get? "__c0" = some (.int (ttpResult mid)) :=
    store_get_self _ _ _
  have hprice' : Lres.get? "price" = some (.int (Int.ofNat p)) := by
    rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "price") = false),
      hLmid, store_get_ne _ _ (by decide : ("mid" == "price") = false)]
    exact hprice
  have hmidL' : Lres.get? "mid" = some (.int (Int.ofNat mid)) := by
    rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "mid") = false)]
    exact store_get_self _ _ _
  have hlowL' : Lres.get? "low" = some (.int (Int.ofNat low)) := by
    rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "low") = false),
      hLmid, store_get_ne _ _ (by decide : ("mid" == "low") = false)]
    exact hlow
  have hhighL' : Lres.get? "high" = some (.int (Int.ofNat high)) := by
    rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "high") = false),
      hLmid, store_get_ne _ _ (by decide : ("mid" == "high") = false)]
    exact hhigh
  have hspL' : Lres.get? "spacing" = some (.int (Int.ofNat s)) := by
    rw [hLres, store_get_ne _ _ (by decide : ("__c0" == "spacing") = false),
      hLmid, store_get_ne _ _ (by decide : ("mid" == "spacing") = false)]
    exact hsp
  have hcond : evalExpr? cfg { caller with locals := Lres } evm
      (.binary .lt (.var "__c0") (.var "price")) =
      .ok (.bool (decide (ttpResult mid < Int.ofNat p))) := by
    simp only [evalExpr?, hc0, hprice', evalBinaryOp?, EvalResult.bind, bind,
      EvalResult.ofOption]
  by_cases hltc : ttpResult mid < Int.ofNat p
  · -- `low := uint256(mid + 1)`
    have hcondT : evalExpr? cfg { caller with locals := Lres } evm
        (.binary .lt (.var "__c0") (.var "price")) = .ok (.bool true) := by
      rw [hcond,
        show decide (ttpResult mid < Int.ofNat p) = true from
          decide_eq_true_iff.mpr hltc]
    have hplus1 : evalExpr? cfg { caller with locals := Lres } evm
        (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S) =
        .ok (.int (Int.ofNat mid + 1)) := by
      have he0 : evalExpr? cfg { caller with locals := Lres } evm
          (.binary .add (.var "mid") (.intLit 1)) = .ok (.int (Int.ofNat mid + 1)) := by
        simp only [evalExpr?, hmidL', evalBinaryOp?, EvalResult.bind, bind,
          EvalResult.ofOption]
      simp only [evalExpr?, he0, EvalResult.bind, bind, EvalResult.ofOption,
        castValue_int]
      have hW : (EVM.twoPow 256 : Nat) = 2 ^ 256 := rfl
      rw [normalizeInt_uint_eq_self _ _ (by
          have h0 : (0 : Int) ≤ Int.ofNat mid := Int.ofNat_nonneg _
          omega) (by
        rw [hW]
        rw [show Int.ofNat mid + 1 = Int.ofNat (mid + 1) from by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]]
        exact Int.ofNat_lt.mpr (by omega))]
    have hass := ExecStmt.assign (Or.inl rfl) hplus1 (assignLocalBase_ok hlowL')
    have hite : ExecStmt cfg { caller with locals := Lres } evm
        (.ite (.binary .lt (.var "__c0") (.var "price"))
          [.assign .localVar { base := "low", steps := [] }
            (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
          [.assign .localVar { base := "high", steps := [] } (.var "mid")])
        (.ok ⟨caller.contract, Lres.insert "low" (.int (Int.ofNat mid + 1)),
            caller.immutables⟩ evm) :=
      ExecStmt.iteTrue hcondT (ExecBlock.consNormal hass ExecBlock.nil)
    refine ⟨mid + 1, high, Lres.insert "low" (.int (Int.ofNat mid + 1)),
      ExecBlock.consNormal (ExecStmt.letDecl hdiv)
        (ExecBlock.consNormal hic (ExecBlock.consNormal hite ExecBlock.nil)),
      ⟨?_, ?_, ?_, ?_, by omega, hh6744⟩, by omega,
      fun _ => ⟨rfl, rfl⟩, fun hn => absurd hltc hn⟩
    · exact store_get_self _ _ _
    · rw [store_get_ne _ _ (by decide : ("low" == "high") = false)]
      exact hhighL'
    · rw [store_get_ne _ _ (by decide : ("low" == "price") = false)]
      exact hprice'
    · rw [store_get_ne _ _ (by decide : ("low" == "spacing") = false)]
      exact hspL'
  · -- `high := mid`
    have hcondF : evalExpr? cfg { caller with locals := Lres } evm
        (.binary .lt (.var "__c0") (.var "price")) = .ok (.bool false) := by
      rw [hcond,
        show decide (ttpResult mid < Int.ofNat p) = false from
          decide_eq_false_iff_not.mpr hltc]
    have hmidE : evalExpr? cfg { caller with locals := Lres } evm (.var "mid") =
        .ok (.int (Int.ofNat mid)) := by
      simp only [evalExpr?, hmidL', EvalResult.ofOption]
    have hass := ExecStmt.assign (Or.inl rfl) hmidE (assignLocalBase_ok hhighL')
    have hite : ExecStmt cfg { caller with locals := Lres } evm
        (.ite (.binary .lt (.var "__c0") (.var "price"))
          [.assign .localVar { base := "low", steps := [] }
            (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
          [.assign .localVar { base := "high", steps := [] } (.var "mid")])
        (.ok ⟨caller.contract, Lres.insert "high" (.int (Int.ofNat mid)),
            caller.immutables⟩ evm) :=
      ExecStmt.iteFalse hcondF (ExecBlock.consNormal hass ExecBlock.nil)
    refine ⟨low, mid, Lres.insert "high" (.int (Int.ofNat mid)),
      ExecBlock.consNormal (ExecStmt.letDecl hdiv)
        (ExecBlock.consNormal hic (ExecBlock.consNormal hite ExecBlock.nil)),
      ⟨?_, ?_, ?_, ?_, hmidle, by omega⟩, by omega,
      fun h => absurd h hltc, fun _ => ⟨rfl, rfl⟩⟩
    · rw [store_get_ne _ _ (by decide : ("high" == "low") = false)]
      exact hlowL'
    · exact store_get_self _ _ _
    · rw [store_get_ne _ _ (by decide : ("high" == "price") = false)]
      exact hprice'
    · rw [store_get_ne _ _ (by decide : ("high" == "spacing") = false)]
      exact hspL'

/-! ### EVM-side loop traces

The loop head at pc 213 carries `[price, high, low, spacing] ++ R`; one iteration is
`213 → 300 → 476 → 486 → wExp-tail → 523 → 446 → 453 → 570 → 319 → 326/337 → 331 → 213`. -/

/-- `shiftRight (ofNat low + ofNat high) 1` is the midpoint word `wordOfInt (Int.ofNat mid)`. -/
theorem p2tMid_word {low high : Nat} (hh : high ≤ 6744) (hl : low ≤ high) :
    UInt256.shiftRight (UInt256.ofNat low + UInt256.ofNat high) (UInt256.ofNat 1) =
      EVM.wordOfInt (Int.ofNat ((low + high) / 2)) := by
  have hle : low + high < UInt256.size :=
    lt_of_le_of_lt (by omega) (by decide : (13488 : Nat) < UInt256.size)
  have hadd : UInt256.ofNat low + UInt256.ofNat high =
      EVM.wordOfInt (Int.ofNat (low + high)) := by
    rw [show UInt256.ofNat low = EVM.wordOfInt (Int.ofNat low) from rfl,
        show UInt256.ofNat high = EVM.wordOfInt (Int.ofNat high) from rfl,
        ← wordOfInt_add]
    rw [show Int.ofNat low + Int.ofNat high = Int.ofNat (low + high) from by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
  rw [hadd,
      show EVM.wordOfInt (Int.ofNat (low + high)) = EVM.wordOfInt ↑(low + high) from rfl,
      ushr1_word (Int.natCast_nonneg _)
        (Int.ofNat_lt.mpr (lt_of_lt_of_le hle (by decide : UInt256.size ≤ EVM.wordModulus))),
      show ↑(low + high) / (2 : Int) = Int.ofNat ((low + high) / 2) from by
        rw [show (2 : Int) = Int.ofNat 2 from rfl]
        simp only [Int.ofNat_eq_natCast]
        rw [Int.ofNat_ediv_ofNat]]

/-- One binary-search iteration where an inner `wExp`-side check reverts:
    the `610 → 456` (divisor zero) or `446 → 456` (denominator zero) path. -/
theorem p2tX_iter_rev {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {pw sw : UInt256} {low high : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024)
    (hlt : low < high) (hhi : high ≤ 6744)
    (hrev0 : (ttpArg ((low + high) / 2) < 0 ∧
        wExpPos (-ttpArg ((low + high) / 2)) = 0) ∨
      ttpDen (wExpVal (ttpArg ((low + high) / 2))) = 0)
    (rd : RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213)
      (pw :: UInt256.ofNat high :: UInt256.ofNat low :: sw :: R) mem aw rdata σ k C) :
    RDrev tickLibWrapperBytecode g s0 := by
  set mid : Nat := (low + high) / 2 with hmid_def
  set midW := UInt256.shiftRight (UInt256.ofNat low + UInt256.ofNat high)
    (UInt256.ofNat 1) with hmidW
  have hmidWn : midW = UInt256.ofNat mid := p2tMid_word hhi (by omega)
  have hmidWtn : midW.toNat = mid := by
    rw [hmidWn]
    exact ulit_toNat' mid (lt_of_le_of_lt (by omega : mid ≤ 6744) (by decide))
  have hmidlt : mid < high := by omega
  have hne : UInt256.sub (UInt256.ofNat low) (UInt256.ofNat high) ≠
      UInt256.ofNat 0 := by
    intro h
    have he := u256_sub_eq_zero_iff_eq (a := UInt256.ofNat low)
      (b := UInt256.ofNat high) |>.mp h
    have h' := congrArg UInt256.toNat he
    rw [ulit_toNat' low (lt_of_le_of_lt (by omega : low ≤ high)
        (lt_of_le_of_lt hhi (by decide : (6744 : Nat) < UInt256.size))),
        ulit_toNat' high (lt_of_le_of_lt hhi (by decide))] at h'
    omega
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_213_taken
    (by simp only [List.length_cons]; omega) hne (by jump_dest) rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_300
    (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_300_stack] at rd2
  have hgt : UInt256.gt midW (UInt256.ofNat 6744) = ⟨0⟩ := by
    apply ugt_zero
    rw [hmidWn, ulit_toNat' mid (lt_of_le_of_lt (by omega : mid ≤ 6744) (by decide)),
      ulit_toNat' 6744 (by decide)]
    omega
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_476_fallthrough
    (by simp only [List.length_cons]; omega) hgt rd2
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_486
    (by simp only [List.length_cons]; omega) (by jump_dest) rd3
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_486_stack] at rd4
  set warg := UInt256.mul (UInt256.ofNat 4987541511039073)
      (UInt256.sub (UInt256.ofNat 3372) midW) with hwarg
  have hsign : EVM.signed warg = ttpArg mid := by
    rw [hwarg]
    exact ttpArg_signed hmidWtn.symm (by omega)
  have hwarg' : warg = EVM.wordOfInt (ttpArg mid) := by
    rw [hwarg]; exact ttpArg_word hmidWtn.symm
  -- shared: given a `610`-or-`446`-taken RD, finish with `block_456`.
  rcases hrev0 with hdz0 | hdz
  · -- `arg < 0 ∧ wExpPos = 0`: 591_fallthrough → 600 → 591_taken → 636 → 610_taken → 456
    have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) = ⟨0⟩ := by
      have hneg : EVM.signed warg < 0 := by rw [hsign]; exact hdz0.1
      have hge := toNat_ge_2pow255_of_signed_neg hneg
      have hs0 : UInt256.slt warg ⟨0⟩ = ⟨1⟩ := by
        show UInt256.slt warg (UInt256.ofNat 0) = ⟨1⟩
        exact slt_lit_one_high (a := warg) (m := 0) (by norm_num) hge
      rw [hs0]
      exact isZero_eq_zero_of_ne (by decide)
    have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough
      (by simp only [List.length_cons]; omega) hslt0 rd4
    have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_600
      (by simp only [List.length_cons]; omega) (by jump_dest) rd5
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd6
    have hneg' : UInt256.sub ⟨0⟩ warg = EVM.wordOfInt (-ttpArg mid) := by
      rw [hwarg', show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, wordOfInt_sub_of]
      exact wordOfInt_cong (by
        rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
    have hslt1 : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩) ≠ ⟨0⟩ := by
      have hs : EVM.signed (UInt256.sub ⟨0⟩ warg) = -ttpArg mid := by
        rw [hneg', signed_wordOfInt]
        have hb := ttpArg_bound (by omega : mid ≤ 6744)
        show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid
        exact sintNorm_of_mem _ (by omega) (by omega)
      have hnn : 0 ≤ EVM.signed (UInt256.sub ⟨0⟩ warg) := by rw [hs]; omega
      have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
      have hs0 : UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩ = ⟨0⟩ := by
        show UInt256.slt (UInt256.sub ⟨0⟩ warg) (UInt256.ofNat 0) = ⟨0⟩
        exact slt_lit_zero (a := UInt256.sub ⟨0⟩ warg) (m := 0) (by norm_num)
          (Nat.zero_le _) hlt2
      rw [hs0]
      decide
    have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken
      (by simp only [List.length_cons]; omega) hslt1 (by jump_dest) rd6
    have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_636
      (by simp only [List.length_cons]; omega) (by jump_dest) rd7
    rw [wExp636_stack, hneg', signed_wordOfInt,
        show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid from
          sintNorm_of_mem _ (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)
            (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)] at rd8
    have hz : UInt256.isZero (EVM.wordOfInt (wExpPos (-ttpArg mid))) ≠ ⟨0⟩ := by
      rw [show EVM.wordOfInt (wExpPos (-ttpArg mid)) = ⟨0⟩ from
        (wordOfInt_wExpPos_eq_zero_iff _).mpr hdz0.2]
      decide
    have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_610_taken
      (by simp only [List.length_cons]; omega) hz (by jump_dest) rd8
    exact tickLibWrapperBlocks.tickLibWrapper_block_456
      (by simp only [List.length_cons]; omega) rd9
  · -- `ttpDen = 0` (divisor may or may not also be zero — take that path when it is).
    by_cases hdz0' : ttpArg mid < 0 ∧ wExpPos (-ttpArg mid) = 0
    · have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) = ⟨0⟩ := by
        have hneg : EVM.signed warg < 0 := by rw [hsign]; exact hdz0'.1
        have hge := toNat_ge_2pow255_of_signed_neg hneg
        have hs0 : UInt256.slt warg ⟨0⟩ = ⟨1⟩ := by
          show UInt256.slt warg (UInt256.ofNat 0) = ⟨1⟩
          exact slt_lit_one_high (a := warg) (m := 0) (by norm_num) hge
        rw [hs0]
        exact isZero_eq_zero_of_ne (by decide)
      have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough
        (by simp only [List.length_cons]; omega) hslt0 rd4
      have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_600
        (by simp only [List.length_cons]; omega) (by jump_dest) rd5
      simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd6
      have hneg' : UInt256.sub ⟨0⟩ warg = EVM.wordOfInt (-ttpArg mid) := by
        rw [hwarg', show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, wordOfInt_sub_of]
        exact wordOfInt_cong (by
          rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
      have hslt1 : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩) ≠ ⟨0⟩ := by
        have hs : EVM.signed (UInt256.sub ⟨0⟩ warg) = -ttpArg mid := by
          rw [hneg', signed_wordOfInt]
          have hb := ttpArg_bound (by omega : mid ≤ 6744)
          show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid
          exact sintNorm_of_mem _ (by omega) (by omega)
        have hnn : 0 ≤ EVM.signed (UInt256.sub ⟨0⟩ warg) := by rw [hs]; omega
        have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
        have hs0 : UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩ = ⟨0⟩ := by
          show UInt256.slt (UInt256.sub ⟨0⟩ warg) (UInt256.ofNat 0) = ⟨0⟩
          exact slt_lit_zero (a := UInt256.sub ⟨0⟩ warg) (m := 0) (by norm_num)
            (Nat.zero_le _) hlt2
        rw [hs0]
        decide
      have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken
        (by simp only [List.length_cons]; omega) hslt1 (by jump_dest) rd6
      have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_636
        (by simp only [List.length_cons]; omega) (by jump_dest) rd7
      rw [wExp636_stack, hneg', signed_wordOfInt,
          show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid from
            sintNorm_of_mem _ (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)
              (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)] at rd8
      have hz : UInt256.isZero (EVM.wordOfInt (wExpPos (-ttpArg mid))) ≠ ⟨0⟩ := by
        rw [show EVM.wordOfInt (wExpPos (-ttpArg mid)) = ⟨0⟩ from
          (wordOfInt_wExpPos_eq_zero_iff _).mpr hdz0'.2]
        decide
      have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_610_taken
        (by simp only [List.length_cons]; omega) hz (by jump_dest) rd8
      exact tickLibWrapperBlocks.tickLibWrapper_block_456
        (by simp only [List.length_cons]; omega) rd9
    · have hbound : ttpArg mid < 0 → wExpPos (-ttpArg mid) ≠ 0 :=
        fun hn hz => hdz0' ⟨hn, hz⟩
      by_cases harg0 : ttpArg mid < 0
      · -- negative arg, `wExpPos ≠ 0`: 591_ft → 600 → 591_taken → 636 → 610_ft → 617 → 523
        have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) = ⟨0⟩ := by
          have hneg : EVM.signed warg < 0 := by rw [hsign]; exact harg0
          have hge := toNat_ge_2pow255_of_signed_neg hneg
          have hs0 : UInt256.slt warg ⟨0⟩ = ⟨1⟩ := by
            show UInt256.slt warg (UInt256.ofNat 0) = ⟨1⟩
            exact slt_lit_one_high (a := warg) (m := 0) (by norm_num) hge
          rw [hs0]
          exact isZero_eq_zero_of_ne (by decide)
        have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough
          (by simp only [List.length_cons]; omega) hslt0 rd4
        have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_600
          (by simp only [List.length_cons]; omega) (by jump_dest) rd5
        simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd6
        have hneg' : UInt256.sub ⟨0⟩ warg = EVM.wordOfInt (-ttpArg mid) := by
          rw [hwarg', show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, wordOfInt_sub_of]
          exact wordOfInt_cong (by
            rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
        have hslt1 : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩) ≠ ⟨0⟩ := by
          have hs : EVM.signed (UInt256.sub ⟨0⟩ warg) = -ttpArg mid := by
            rw [hneg', signed_wordOfInt]
            have hb := ttpArg_bound (by omega : mid ≤ 6744)
            show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid
            exact sintNorm_of_mem _ (by omega) (by omega)
          have hnn : 0 ≤ EVM.signed (UInt256.sub ⟨0⟩ warg) := by rw [hs]; omega
          have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
          have hs0 : UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩ = ⟨0⟩ := by
            show UInt256.slt (UInt256.sub ⟨0⟩ warg) (UInt256.ofNat 0) = ⟨0⟩
            exact slt_lit_zero (a := UInt256.sub ⟨0⟩ warg) (m := 0) (by norm_num)
              (Nat.zero_le _) hlt2
          rw [hs0]
          decide
        have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken
          (by simp only [List.length_cons]; omega) hslt1 (by jump_dest) rd6
        have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_636
          (by simp only [List.length_cons]; omega) (by jump_dest) rd7
        rw [wExp636_stack, hneg', signed_wordOfInt,
            show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid from
              sintNorm_of_mem _ (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)
                (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)] at rd8
        have hz : UInt256.isZero (EVM.wordOfInt (wExpPos (-ttpArg mid))) = ⟨0⟩ := by
          exact isZero_eq_zero_of_ne (fun hz' =>
            hbound harg0 ((wordOfInt_wExpPos_eq_zero_iff _).mp hz'))
        have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_610_fallthrough
          (by simp only [List.length_cons]; omega) hz rd8
        have rd10 := tickLibWrapperBlocks.tickLibWrapper_block_617
          (by simp only [List.length_cons]; omega) (by jump_dest) rd9
        simp only [tickLibWrapperBlocks.tickLibWrapper_block_617_stack,
          wExpVal_div_word _ harg0] at rd10
        have rd523 := tickLibWrapperBlocks.tickLibWrapper_block_523
          (by simp only [List.length_cons]; omega) (by jump_dest) rd10
        simp only [tickLibWrapperBlocks.tickLibWrapper_block_523_stack] at rd523
        have hdz' : UInt256.isZero (UInt256.ofNat 1000000000000000000 +
            EVM.wordOfInt (wExpVal (ttpArg mid))) ≠ ⟨0⟩ := by
          rw [ttpDen_word,
              show EVM.wordOfInt (ttpDen (wExpVal (ttpArg mid))) = ⟨0⟩ from
                (wordOfInt_uNorm_eq_zero_iff _).mpr hdz]
          decide
        have rd446 := tickLibWrapperBlocks.tickLibWrapper_block_446_taken
          (by simp only [List.length_cons]; omega) hdz' (by jump_dest) rd523
        exact tickLibWrapperBlocks.tickLibWrapper_block_456
          (by simp only [List.length_cons]; omega) rd446
      · -- `arg ≥ 0`: 591_taken → 636 → 523 → 446_taken → 456
        have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) ≠ ⟨0⟩ := by
          have hnn : 0 ≤ EVM.signed warg := by rw [hsign]; omega
          have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
          have hs0 : UInt256.slt warg ⟨0⟩ = ⟨0⟩ := by
            show UInt256.slt warg (UInt256.ofNat 0) = ⟨0⟩
            exact slt_lit_zero (a := warg) (m := 0) (by norm_num) (Nat.zero_le _) hlt2
          rw [hs0]
          decide
        have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken
          (by simp only [List.length_cons]; omega) hslt0 (by jump_dest) rd4
        have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_636
          (by simp only [List.length_cons]; omega) (by jump_dest) rd5
        rw [wExp636_stack, hwarg', signed_wordOfInt,
            show normalizeInt sint256T (ttpArg mid) = ttpArg mid from
              ttpArg_sintNorm (by omega : mid ≤ 6744),
            show wExpPos (ttpArg mid) = wExpVal (ttpArg mid) from by
              unfold wExpVal; rw [if_neg harg0]] at rd6
        have rd523 := tickLibWrapperBlocks.tickLibWrapper_block_523
          (by simp only [List.length_cons]; omega) (by jump_dest) rd6
        simp only [tickLibWrapperBlocks.tickLibWrapper_block_523_stack] at rd523
        have hdz' : UInt256.isZero (UInt256.ofNat 1000000000000000000 +
            EVM.wordOfInt (wExpVal (ttpArg mid))) ≠ ⟨0⟩ := by
          rw [ttpDen_word,
              show EVM.wordOfInt (ttpDen (wExpVal (ttpArg mid))) = ⟨0⟩ from
                (wordOfInt_uNorm_eq_zero_iff _).mpr hdz]
          decide
        have rd446 := tickLibWrapperBlocks.tickLibWrapper_block_446_taken
          (by simp only [List.length_cons]; omega) hdz' (by jump_dest) rd523
        exact tickLibWrapperBlocks.tickLibWrapper_block_456
          (by simp only [List.length_cons]; omega) rd446

/-- One binary-search iteration when the inner call succeeds: lands back at pc 213 with
    `low := mid + 1` (when `ttpResult mid < price`) or `high := mid`. -/
theorem p2tX_iter {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {pw sw : UInt256} {low high : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024)
    (hlt : low < high) (hhi : high ≤ 6744)
    (hb0 : ¬ (ttpArg ((low + high) / 2) < 0 ∧
        wExpPos (-ttpArg ((low + high) / 2)) = 0))
    (hd : ttpDen (wExpVal (ttpArg ((low + high) / 2))) ≠ 0)
    (rd : RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213)
      (pw :: UInt256.ofNat high :: UInt256.ofNat low :: sw :: R) mem aw rdata σ k C) :
    ∃ k' C', RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213)
      (pw ::
        (if (ttpResult ((low + high) / 2)).toNat < pw.toNat
          then UInt256.ofNat high else UInt256.ofNat ((low + high) / 2)) ::
        (if (ttpResult ((low + high) / 2)).toNat < pw.toNat
          then UInt256.ofNat ((low + high) / 2 + 1) else UInt256.ofNat low) ::
        sw :: R) mem aw rdata σ k' C' := by
  set mid : Nat := (low + high) / 2 with hmid_def
  set midW := UInt256.shiftRight (UInt256.ofNat low + UInt256.ofNat high)
    (UInt256.ofNat 1) with hmidW
  have hmidWn : midW = UInt256.ofNat mid := p2tMid_word hhi (by omega)
  have hmidWtn : midW.toNat = mid := by
    rw [hmidWn]
    exact ulit_toNat' mid (lt_of_le_of_lt (by omega : mid ≤ 6744) (by decide))
  have hmidlt : mid < high := by omega
  have hne : UInt256.sub (UInt256.ofNat low) (UInt256.ofNat high) ≠
      UInt256.ofNat 0 := by
    intro h
    have he := u256_sub_eq_zero_iff_eq (a := UInt256.ofNat low)
      (b := UInt256.ofNat high) |>.mp h
    have h' := congrArg UInt256.toNat he
    rw [ulit_toNat' low (lt_of_le_of_lt (by omega : low ≤ high)
        (lt_of_le_of_lt hhi (by decide : (6744 : Nat) < UInt256.size))),
        ulit_toNat' high (lt_of_le_of_lt hhi (by decide))] at h'
    omega
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_213_taken
    (by simp only [List.length_cons]; omega) hne (by jump_dest) rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_300
    (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_300_stack] at rd2
  have hgt : UInt256.gt midW (UInt256.ofNat 6744) = ⟨0⟩ := by
    apply ugt_zero
    rw [hmidWn, ulit_toNat' mid (lt_of_le_of_lt (by omega : mid ≤ 6744) (by decide)),
      ulit_toNat' 6744 (by decide)]
    omega
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_476_fallthrough
    (by simp only [List.length_cons]; omega) hgt rd2
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_486
    (by simp only [List.length_cons]; omega) (by jump_dest) rd3
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_486_stack] at rd4
  set warg := UInt256.mul (UInt256.ofNat 4987541511039073)
      (UInt256.sub (UInt256.ofNat 3372) midW) with hwarg
  have hsign : EVM.signed warg = ttpArg mid := by
    rw [hwarg]
    exact ttpArg_signed hmidWtn.symm (by omega)
  have hwarg' : warg = EVM.wordOfInt (ttpArg mid) := by
    rw [hwarg]; exact ttpArg_word hmidWtn.symm
  -- wExp tail to pc 523
  have h523 : ∃ k' C', RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 523)
      (EVM.wordOfInt (wExpVal (ttpArg mid)) :: (UInt256.ofNat 570) ::
        (UInt256.ofNat 49999999999) :: (UInt256.ofNat 100000000000) ::
        (UInt256.ofNat 100000000000) :: (UInt256.ofNat 319) :: pw ::
        UInt256.ofNat low :: midW :: pw :: UInt256.ofNat high :: sw :: R)
      mem aw rdata σ k' C' := by
    by_cases harg0 : ttpArg mid < 0
    · have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) = ⟨0⟩ := by
        have hneg : EVM.signed warg < 0 := by rw [hsign]; exact harg0
        have hge := toNat_ge_2pow255_of_signed_neg hneg
        have hs0 : UInt256.slt warg ⟨0⟩ = ⟨1⟩ := by
          show UInt256.slt warg (UInt256.ofNat 0) = ⟨1⟩
          exact slt_lit_one_high (a := warg) (m := 0) (by norm_num) hge
        rw [hs0]
        exact isZero_eq_zero_of_ne (by decide)
      have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_591_fallthrough
        (by simp only [List.length_cons]; omega) hslt0 rd4
      have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_600
        (by simp only [List.length_cons]; omega) (by jump_dest) rd5
      simp only [tickLibWrapperBlocks.tickLibWrapper_block_600_stack] at rd6
      have hneg' : UInt256.sub ⟨0⟩ warg = EVM.wordOfInt (-ttpArg mid) := by
        rw [hwarg', show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, wordOfInt_sub_of]
        exact wordOfInt_cong (by
          rw [show Int.ofNat EVM.wordModulus = (2 ^ 256 : Int) from rfl]; omega)
      have hslt1 : UInt256.isZero (UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩) ≠ ⟨0⟩ := by
        have hs : EVM.signed (UInt256.sub ⟨0⟩ warg) = -ttpArg mid := by
          rw [hneg', signed_wordOfInt]
          have hb := ttpArg_bound (by omega : mid ≤ 6744)
          show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid
          exact sintNorm_of_mem _ (by omega) (by omega)
        have hnn : 0 ≤ EVM.signed (UInt256.sub ⟨0⟩ warg) := by rw [hs]; omega
        have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
        have hs0 : UInt256.slt (UInt256.sub ⟨0⟩ warg) ⟨0⟩ = ⟨0⟩ := by
          show UInt256.slt (UInt256.sub ⟨0⟩ warg) (UInt256.ofNat 0) = ⟨0⟩
          exact slt_lit_zero (a := UInt256.sub ⟨0⟩ warg) (m := 0) (by norm_num)
            (Nat.zero_le _) hlt2
        rw [hs0]
        decide
      have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken
        (by simp only [List.length_cons]; omega) hslt1 (by jump_dest) rd6
      have rd8 := tickLibWrapperBlocks.tickLibWrapper_block_636
        (by simp only [List.length_cons]; omega) (by jump_dest) rd7
      rw [wExp636_stack, hneg', signed_wordOfInt,
          show normalizeInt sint256T (-ttpArg mid) = -ttpArg mid from
            sintNorm_of_mem _ (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)
              (by have := ttpArg_bound (by omega : mid ≤ 6744); omega)] at rd8
      have hz : UInt256.isZero (EVM.wordOfInt (wExpPos (-ttpArg mid))) = ⟨0⟩ := by
        exact isZero_eq_zero_of_ne (fun hz' =>
          hb0 ⟨harg0, (wordOfInt_wExpPos_eq_zero_iff _).mp hz'⟩)
      have rd9 := tickLibWrapperBlocks.tickLibWrapper_block_610_fallthrough
        (by simp only [List.length_cons]; omega) hz rd8
      have rd10 := tickLibWrapperBlocks.tickLibWrapper_block_617
        (by simp only [List.length_cons]; omega) (by jump_dest) rd9
      exact ⟨_, _, by simpa only [tickLibWrapperBlocks.tickLibWrapper_block_617_stack,
        wExpVal_div_word _ harg0] using rd10⟩
    · have hslt0 : UInt256.isZero (UInt256.slt warg ⟨0⟩) ≠ ⟨0⟩ := by
        have hnn : 0 ≤ EVM.signed warg := by rw [hsign]; omega
        have hlt2 := toNat_lt_2pow255_of_signed_nonneg hnn
        have hs0 : UInt256.slt warg ⟨0⟩ = ⟨0⟩ := by
          show UInt256.slt warg (UInt256.ofNat 0) = ⟨0⟩
          exact slt_lit_zero (a := warg) (m := 0) (by norm_num) (Nat.zero_le _) hlt2
        rw [hs0]
        decide
      have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_591_taken
        (by simp only [List.length_cons]; omega) hslt0 (by jump_dest) rd4
      have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_636
        (by simp only [List.length_cons]; omega) (by jump_dest) rd5
      exact ⟨_, _, by rwa [wExp636_stack, hwarg', signed_wordOfInt,
          show normalizeInt sint256T (ttpArg mid) = ttpArg mid from
            ttpArg_sintNorm (by omega : mid ≤ 6744),
          show wExpPos (ttpArg mid) = wExpVal (ttpArg mid) from by
            unfold wExpVal; rw [if_neg harg0]] at rd6⟩
  obtain ⟨k5, C5, rd523⟩ := h523
  have rd523' := tickLibWrapperBlocks.tickLibWrapper_block_523
    (by simp only [List.length_cons]; omega) (by jump_dest) rd523
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_523_stack] at rd523'
  have hzz : UInt256.isZero (UInt256.ofNat 1000000000000000000 +
      EVM.wordOfInt (wExpVal (ttpArg mid))) = ⟨0⟩ := by
    rw [ttpDen_word]
    apply isZero_eq_zero_of_ne
    intro hz'
    exact hd ((wordOfInt_uNorm_eq_zero_iff _).mp hz')
  have rd446 := tickLibWrapperBlocks.tickLibWrapper_block_446_fallthrough
    (by simp only [List.length_cons]; omega) hzz rd523'
  have rd453 := tickLibWrapperBlocks.tickLibWrapper_block_453
    (by simp only [List.length_cons]; omega) (by jump_dest) rd446
  have rd570 := tickLibWrapperBlocks.tickLibWrapper_block_570
    (by simp only [List.length_cons]; omega) (by jump_dest) rd453
  simp only [tickLibWrapperBlocks.tickLibWrapper_block_570_stack] at rd570
  have hres := ttpResult_word mid hd
  rw [hres] at rd570
  -- rd570 : RD 319 (wordOfInt (ttpResult mid) :: pw :: low :: midW :: pw :: high :: sw :: R)
  have htn : (EVM.wordOfInt (ttpResult mid)).toNat = (ttpResult mid).toNat := by
    simpa using congrArg Int.toNat (ttpResult_toNat mid)
  by_cases hltc : (ttpResult mid).toNat < pw.toNat
  · -- `__c0 < price`: 319 fallthrough → 326 → 331 → 213, `low := mid + 1`.
    have hltw : UInt256.lt (EVM.wordOfInt (ttpResult mid)) pw = ⟨1⟩ := by
      apply ult_one
      rw [htn]
      exact hltc
    have hisz : UInt256.isZero (UInt256.lt (EVM.wordOfInt (ttpResult mid)) pw) =
        ⟨0⟩ := by rw [hltw]; decide
    have rd319 := tickLibWrapperBlocks.tickLibWrapper_block_319_fallthrough
      (by simp only [List.length_cons]; omega) hisz rd570
    have rd326 := tickLibWrapperBlocks.tickLibWrapper_block_326
      (by simp only [List.length_cons]; omega) rd319
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_326_stack] at rd326
    have h1mid : UInt256.ofNat 1 + midW = UInt256.ofNat (mid + 1) := by
      rw [hmidWn]
      apply u256_inj
      rw [uadd_toNat, ulit_toNat' 1 (by decide),
          ulit_toNat' mid (lt_of_le_of_lt (by omega : mid ≤ 6744) (by decide)),
          ulit_toNat' (mid + 1) (lt_of_le_of_lt (by omega : mid + 1 ≤ 6745)
            (by decide : (6745 : Nat) < UInt256.size))]
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega : 1 + mid ≤ 6745)
        (by decide : (6745 : Nat) < UInt256.size))]
      omega
    rw [h1mid] at rd326
    have rd331 := tickLibWrapperBlocks.tickLibWrapper_block_331
      (by simp only [List.length_cons]; omega) (by jump_dest) rd326
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_331_stack] at rd331
    exact ⟨_, _, by rw [if_pos hltc, if_pos hltc]; exact rd331⟩
  · -- `__c0 ≥ price`: 319 taken → 337 → 331 → 213, `high := mid`.
    have hltw : UInt256.lt (EVM.wordOfInt (ttpResult mid)) pw = ⟨0⟩ := by
      apply ult_zero
      rw [htn]
      exact le_of_not_gt hltc
    have hisz : UInt256.isZero (UInt256.lt (EVM.wordOfInt (ttpResult mid)) pw) ≠
        ⟨0⟩ := by rw [hltw]; decide
    have rd319 := tickLibWrapperBlocks.tickLibWrapper_block_319_taken
      (by simp only [List.length_cons]; omega) hisz (by jump_dest) rd570
    have rd337 := tickLibWrapperBlocks.tickLibWrapper_block_337
      (by simp only [List.length_cons]; omega) (by jump_dest) rd319
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_337_stack] at rd337
    rw [hmidWn] at rd337
    have rd331 := tickLibWrapperBlocks.tickLibWrapper_block_331
      (by simp only [List.length_cons]; omega) (by jump_dest) rd337
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_331_stack] at rd331
    exact ⟨_, _, by rw [if_neg hltc, if_neg hltc]; exact rd331⟩

/-- The `while`-body statement list of `priceToTick_body`, shared by the coupled-loop lemmas. -/
private abbrev p2tLoopBodyStmts : List Stmt :=
  [.letDecl "mid" none
    (.binary .div
      (.cast (.binary .add (.var "low") (.var "high")) uint256S) (.intLit 2)),
   .internalCall "tickToPrice_body" [.var "mid"] "__c0",
   .ite (.binary .lt (.var "__c0") (.var "price"))
     [.assign .localVar { base := "low", steps := [] }
       (.cast (.binary .add (.var "mid") (.intLit 1)) uint256S)]
     [.assign .localVar { base := "high", steps := [] } (.var "mid")]]

/-- Coupled binary-search loop: the Stele `while` and the EVM `213` loop agree — either the
    loop exits at `low = high` (Stele `whileFalse`, EVM `213 → 221`), or an iteration reverts
    on both sides (the inner `tickToPrice_body(mid)` call).  Fuel induction on `n`. -/
theorem p2tX_loop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {cfg : Config} {caller : Frame} {evm : EVM.State}
    {pw sw : UInt256} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024)
    (p s : Nat) (hpw : pw.toNat = p) (hsw : sw.toNat = s)
    (hcontract : caller.contract = contract) :
    ∀ (n low high : Nat) (L : Store) (k C : Nat),
      L.get? "low" = some (.int (Int.ofNat low)) →
      L.get? "high" = some (.int (Int.ofNat high)) →
      L.get? "price" = some (.int (Int.ofNat p)) →
      L.get? "spacing" = some (.int (Int.ofNat s)) →
      low ≤ high → high ≤ 6744 → high - low ≤ n →
      RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213)
        (pw :: UInt256.ofNat high :: UInt256.ofNat low :: sw :: R) mem aw rdata σ k C →
      (∃ (low' : Nat) (L' : Store) (k' C' : Nat),
        ExecStmt cfg { caller with locals := L } evm
          (.while (.binary .ne (.var "low") (.var "high")) p2tLoopBodyStmts)
          (.ok { caller with locals := L' } evm) ∧
        L'.get? "low" = some (.int (Int.ofNat low')) ∧
        L'.get? "high" = some (.int (Int.ofNat low')) ∧
        L'.get? "price" = some (.int (Int.ofNat p)) ∧
        L'.get? "spacing" = some (.int (Int.ofNat s)) ∧
        low' ≤ 6744 ∧
        RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 221)
          (pw :: UInt256.ofNat low' :: UInt256.ofNat low' :: sw :: R) mem aw rdata σ k' C') ∨
      (ExecStmt cfg { caller with locals := L } evm
          (.while (.binary .ne (.var "low") (.var "high")) p2tLoopBodyStmts) .reverted ∧
        RDrev tickLibWrapperBytecode g s0) := by
  have hcondF : ∀ (L : Store) (m : Nat),
      L.get? "low" = some (.int (Int.ofNat m)) →
      L.get? "high" = some (.int (Int.ofNat m)) →
      evalExpr? cfg { caller with locals := L } evm
        (.binary .ne (.var "low") (.var "high")) = .ok (.bool false) := by
    intro L m hlow hhigh
    simp only [evalExpr?, hlow, hhigh, evalBinaryOp?, EvalResult.bind, bind,
      EvalResult.ofOption]
    have hb : (decide ((Value.int (Int.ofNat m)) = (Value.int (Int.ofNat m)))) = true :=
      decide_eq_true_iff.mpr rfl
    show EvalResult.ok (Value.bool (!(decide
        ((Value.int (Int.ofNat m)) = (Value.int (Int.ofNat m)))))) =
      EvalResult.ok (Value.bool false)
    rw [hb]
    rfl
  have hcondT : ∀ (L : Store) (l h : Nat), l ≠ h →
      L.get? "low" = some (.int (Int.ofNat l)) →
      L.get? "high" = some (.int (Int.ofNat h)) →
      evalExpr? cfg { caller with locals := L } evm
        (.binary .ne (.var "low") (.var "high")) = .ok (.bool true) := by
    intro L l h hne hlow hhigh
    simp only [evalExpr?, hlow, hhigh, evalBinaryOp?, EvalResult.bind, bind,
      EvalResult.ofOption]
    have hb : (decide ((Value.int (Int.ofNat l)) = (Value.int (Int.ofNat h)))) = false :=
      decide_eq_false_iff_not.mpr (fun hc =>
        hne (Int.ofNat_inj.mp (by injection hc)))
    show EvalResult.ok (Value.bool (!(decide
        ((Value.int (Int.ofNat l)) = (Value.int (Int.ofNat h)))))) =
      EvalResult.ok (Value.bool true)
    rw [hb]
    rfl
  intro n
  induction n with
  | zero =>
    intro low high L k C hlow hhigh hprice hsp hle hhi hd rd
    have heq : low = high := by omega
    left
    have hlow' : L.get? "low" = some (.int (Int.ofNat high)) := by
      rw [← heq]; exact hlow
    have hw : ExecStmt cfg { caller with locals := L } evm
        (.while (.binary .ne (.var "low") (.var "high")) p2tLoopBodyStmts)
        (.ok { caller with locals := L } evm) :=
      ExecStmt.whileFalse (hcondF L high hlow' hhigh)
    have hsub : UInt256.sub (UInt256.ofNat low) (UInt256.ofNat high) =
        UInt256.ofNat 0 :=
      u256_sub_eq_zero_iff_eq.mpr (by rw [heq])
    have rd' := tickLibWrapperBlocks.tickLibWrapper_block_213_fallthrough
      (by (try simp only [List.length_cons]); omega) hsub rd
    rw [heq] at rd'
    exact ⟨high, L, _, _, hw, hlow', hhigh, hprice, hsp, hhi, rd'⟩
  | succ n ih =>
    intro low high L k C hlow hhigh hprice hsp hle hhi hd rd
    by_cases heq : low = high
    · left
      have hlow' : L.get? "low" = some (.int (Int.ofNat high)) := by
        rw [← heq]; exact hlow
      have hw : ExecStmt cfg { caller with locals := L } evm
          (.while (.binary .ne (.var "low") (.var "high")) p2tLoopBodyStmts)
          (.ok { caller with locals := L } evm) :=
        ExecStmt.whileFalse (hcondF L high hlow' hhigh)
      have hsub : UInt256.sub (UInt256.ofNat low) (UInt256.ofNat high) =
          UInt256.ofNat 0 :=
        u256_sub_eq_zero_iff_eq.mpr (by rw [heq])
      have rd' := tickLibWrapperBlocks.tickLibWrapper_block_213_fallthrough
        (by (try simp only [List.length_cons]); omega) hsub rd
      rw [heq] at rd'
      exact ⟨high, L, _, _, hw, hlow', hhigh, hprice, hsp, hhi, rd'⟩
    · have hlt : low < high := by omega
      have hcond := hcondT L low high heq hlow hhigh
      by_cases hrev0 : (ttpArg ((low + high) / 2) < 0 ∧
          wExpPos (-ttpArg ((low + high) / 2)) = 0) ∨
          ttpDen (wExpVal (ttpArg ((low + high) / 2))) = 0
      · right
        exact ⟨ExecStmt.whileRevert hcond
            (p2tStep_rev cfg caller evm low high L hcontract hlow hhigh hle hhi hlt hrev0),
          p2tX_iter_rev hstack hlt hhi hrev0 rd⟩
      · obtain ⟨hb0, hd0⟩ := not_or.mp hrev0
        obtain ⟨low', high', L', hblock, ⟨gl', gh', gp', gs', hle', hhi'⟩, hdec, hT, hF⟩ :=
          p2tStep_ok cfg caller evm p s low high L hcontract hlow hhigh hprice hsp
            hle hhi hlt hb0 hd0
        obtain ⟨k', C', rd'⟩ := p2tX_iter hstack hlt hhi hb0 hd0 rd
        have hrnn := ttpResult_nonneg ((low + high) / 2)
        have hcmp : ((ttpResult ((low + high) / 2)).toNat < pw.toNat) ↔
            (ttpResult ((low + high) / 2) < Int.ofNat p) := by
          rw [hpw, show Int.ofNat p = (p : Int) from rfl]
          omega
        by_cases hc : ttpResult ((low + high) / 2) < Int.ofNat p
        · have hcw : (ttpResult ((low + high) / 2)).toNat < pw.toNat := hcmp.mpr hc
          rw [if_pos hcw, if_pos hcw] at rd'
          obtain ⟨e1, e2⟩ := hT hc
          rw [← e1, ← e2] at rd'
          rcases ih low' high' L' k' C' gl' gh' gp' gs' hle' hhi'
              (by omega) rd' with
            ⟨lf, Lf, k2, C2, hw, e1, e2, e3, e4, e5, rdExit⟩ | ⟨hw, hrev⟩
          · exact Or.inl ⟨lf, Lf, k2, C2,
              ExecStmt.whileTrue hcond hblock hw, e1, e2, e3, e4, e5, rdExit⟩
          · exact Or.inr ⟨ExecStmt.whileTrue hcond hblock hw, hrev⟩
        · have hcw : ¬ (ttpResult ((low + high) / 2)).toNat < pw.toNat :=
            fun h => hc (hcmp.mp h)
          rw [if_neg hcw, if_neg hcw] at rd'
          obtain ⟨e1, e2⟩ := hF hc
          rw [← e2, ← e1] at rd'
          rcases ih low' high' L' k' C' gl' gh' gp' gs' hle' hhi'
              (by omega) rd' with
            ⟨lf, Lf, k2, C2, hw, e1, e2, e3, e4, e5, rdExit⟩ | ⟨hw, hrev⟩
          · exact Or.inl ⟨lf, Lf, k2, C2,
              ExecStmt.whileTrue hcond hblock hw, e1, e2, e3, e4, e5, rdExit⟩
          · exact Or.inr ⟨ExecStmt.whileTrue hcond hblock hw, hrev⟩

/-- Successful post-loop tail: `221 → 233 → 244 → 446 → 453 → 253 → 270` returns
    `wordOfInt (pttResult low s)` when `1 ≤ low + s < 2^256` and `s ≠ 0`. -/
theorem p2tX_tail_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {pw sw xhi : UInt256} {low s : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024)
    (hsw : sw.toNat = s)
    (hmem : mem = (UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty
      (UInt256.ofNat 64).toNat 32)
    (hlt : low + s < UInt256.size) (h1 : 1 ≤ low + s) (hs : s ≠ 0)
    (rd : RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 221)
      (pw :: xhi :: UInt256.ofNat low :: sw :: R) mem aw rdata σ k C) :
    RDret tickLibWrapperBytecode g s0 σ
      (EVM.wordOfInt (pttResult (Int.ofNat low) (Int.ofNat s))).toByteArray := by
  set x := UInt256.ofNat low + sw with hx
  have hxT : x.toNat = low + s := by
    rw [hx, uadd_toNat, ulit_toNat' low (by omega), hsw]
    exact Nat.mod_eq_of_lt hlt
  have h221 : UInt256.gt (UInt256.ofNat low) x = ⟨0⟩ := by
    apply ugt_zero
    rw [hxT, ulit_toNat' low (by omega)]; omega
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_221_fallthrough
    (by (try simp only [List.length_cons]); omega) h221 rd
  have hsub1 : (x + UInt256.lnot ⟨0⟩).toNat = low + s - 1 := by
    rw [uadd_toNat, hxT, lnot_toNat_gen,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide]
    have hsz : UInt256.size = 2 ^ 256 := rfl
    rw [show low + s + (2 ^ 256 - 1 - 0) = low + s - 1 + UInt256.size from by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have h233 : UInt256.gt (x + UInt256.lnot ⟨0⟩) x = ⟨0⟩ := by
    apply ugt_zero
    rw [hsub1, hxT]; omega
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_233_fallthrough
    (by (try simp only [List.length_cons]); omega) h233 rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_244
    (by (try simp only [List.length_cons]); omega) (by jump_dest) rd2
  have h446 : UInt256.isZero sw = ⟨0⟩ := by
    apply isZero_eq_zero_of_ne
    intro hz
    apply hs
    rw [← hsw, hz]
    decide
  have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_446_fallthrough
    (by (try simp only [List.length_cons]); omega) h446 rd3
  have rd5 := tickLibWrapperBlocks.tickLibWrapper_block_453
    (by (try simp only [List.length_cons]); omega) (by jump_dest) rd4
  set q := UInt256.div (x + UInt256.lnot ⟨0⟩) sw with hq
  set qn := (low + s - 1) / s with hqn
  have hqT : q.toNat = qn := by rw [hq, udiv_toNat, hsub1, hsw]
  have hqslt : qn * s < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ s) (by omega)
  have hmulq : (UInt256.mul q sw).toNat = qn * s := by
    rw [u256_mul_toNat, hqT, hsw]
    exact Nat.mod_eq_of_lt hqslt
  have h253 : UInt256.isZero (UInt256.lor (UInt256.isZero q)
      (UInt256.eq (UInt256.div (UInt256.mul q sw) q) sw)) = ⟨0⟩ := by
    by_cases hqn0 : qn = 0
    · have hq0 : q = ⟨0⟩ := by
        apply u256_inj
        rw [hqT, hqn0]; decide
      rw [hq0, show UInt256.isZero ⟨0⟩ = ⟨1⟩ from by decide]
      exact isZero_eq_zero_of_ne (u256_lor_one_ne_zero _)
    · have hq0 : UInt256.isZero q = ⟨0⟩ := by
        apply isZero_eq_zero_of_ne
        intro hz
        rw [hz, show (⟨0⟩ : UInt256).toNat = 0 from by decide] at hqT
        exact hqn0 hqT.symm
      have hdiv : UInt256.div (UInt256.mul q sw) q = sw := by
        apply u256_inj
        rw [udiv_toNat, hmulq, hqT]
        show qn * s / qn = sw.toNat
        rw [hsw]
        show qn * s / qn = s
        rw [Nat.mul_comm qn s]
        exact Nat.mul_div_cancel _ (by omega : 0 < qn)
      rw [hq0, hdiv, uInt256_eq_self sw]
      decide
  have rd6 := tickLibWrapperBlocks.tickLibWrapper_block_253_fallthrough
    (by (try simp only [List.length_cons]); omega) h253 rd5
  have rd7 := tickLibWrapperBlocks.tickLibWrapper_block_270
    (by (try simp only [List.length_cons]); omega) rd6
  rw [hmem] at rd7
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide, dispatchMemLoad64] at rd7
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      show (UInt256.ofNat 32).toNat = 32 from by decide] at rd7
  have hmemsize : ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32).size =
      96 := toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
      (lt_usize _ (by decide)) (by decide)
  rw [toByteArray_write_read_back_of_gap _ _ 128
      (by rw [hmemsize]; exact lt_usize _ (by decide))] at rd7
  -- `mul q sw = wordOfInt (pttResult low s)`
  have hptt : pttResult (Int.ofNat low) (Int.ofNat s) = Int.ofNat (qn * s) := by
    show ((Int.ofNat low + Int.ofNat s - 1) / Int.ofNat s) * Int.ofNat s =
      Int.ofNat (qn * s)
    have e1 : Int.ofNat low + Int.ofNat s - 1 = Int.ofNat (low + s - 1) := by
      rw [show Int.ofNat (low + s - 1) = Int.ofNat (low + s) - Int.ofNat 1 from by
        simp only [Int.ofNat_eq_natCast]
        rw [Int.ofNat_sub h1]]
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    rw [e1]
    simp only [Int.ofNat_eq_natCast]
    rw [Int.ofNat_ediv_ofNat, ← Nat.cast_mul]
  have hres : UInt256.mul q sw =
      EVM.wordOfInt (pttResult (Int.ofNat low) (Int.ofNat s)) := by
    rw [hptt, wordOfInt_ofNat_eq]
    apply u256_inj
    rw [hmulq, ulit_toNat' _ hqslt]
  rwa [hres] at rd7

/-- Reverting post-loop tail: `221`-taken (add overflow), `233`-taken (`low + s - 1`
    underflow), or `446`-taken (`spacing = 0`) each end in the panic reverts at `280`/`456`. -/
theorem p2tX_tail_rev {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    {pw sw xhi : UInt256} {low s : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024)
    (hsw : sw.toNat = s) (hlow : low ≤ 6744)
    (hcase : UInt256.size ≤ low + s ∨ low + s = 0 ∨ (s = 0 ∧ 1 ≤ low + s))
    (rd : RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 221)
      (pw :: xhi :: UInt256.ofNat low :: sw :: R) mem aw rdata σ k C) :
    RDrev tickLibWrapperBytecode g s0 := by
  set x := UInt256.ofNat low + sw with hx
  have hslt : s < UInt256.size := by rw [← hsw]; exact sw.val.isLt
  rcases hcase with hov | hz | ⟨hs0, h1⟩
  · have hsz2 : (6744 : Nat) < UInt256.size := by decide
    -- `(low + s) mod 2^256` wrapped below `low`: `221`-taken → `280`.
    have h221 : UInt256.gt (UInt256.ofNat low) x ≠ ⟨0⟩ := by
      have h1' : UInt256.gt (UInt256.ofNat low) x = ⟨1⟩ := by
        apply ugt_one
        rw [hx, uadd_toNat,
          ulit_toNat' low (lt_of_le_of_lt hlow (by decide : (6744:Nat) < UInt256.size)),
          hsw, Nat.mod_eq_sub_mod hov,
          Nat.mod_eq_of_lt (Nat.sub_lt_left_of_lt_add hov (by omega))]
        omega
      rw [h1']; decide
    have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_221_taken
      (by (try simp only [List.length_cons]); omega) h221 (by jump_dest) rd
    exact tickLibWrapperBlocks.tickLibWrapper_block_280
      (by simp only [tickLibWrapperBlocks.tickLibWrapper_block_221_taken_stack,
        List.length_cons, List.length_nil]; omega) rd1
  · -- `low + s = 0`: the `221` add check falls through (`low + 0 = low`), then
    -- `x - 1` underflows at `233` → `280`.
    obtain ⟨rfl, rfl⟩ : low = 0 ∧ s = 0 := by omega
    have h221 : UInt256.gt (UInt256.ofNat 0) x = ⟨0⟩ := by
      apply ugt_zero
      rw [hx, uadd_toNat, ulit_toNat' 0 (by decide), hsw,
        Nat.add_zero, Nat.zero_mod]
    have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_221_fallthrough
      (by (try simp only [List.length_cons]); omega) h221 rd
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_221_fallthrough_stack] at rd1
    have hsub : (x + UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by
      rw [uadd_toNat, hx, uadd_toNat, ulit_toNat' 0 (by decide), hsw,
        lnot_toNat_gen, show (⟨0⟩ : UInt256).toNat = 0 from by decide]
      have hsz : UInt256.size = 2 ^ 256 := rfl
      rw [hsz]; decide
    have h233 : UInt256.gt (x + UInt256.lnot ⟨0⟩) x ≠ ⟨0⟩ := by
      have h1' : UInt256.gt (x + UInt256.lnot ⟨0⟩) x = ⟨1⟩ := by
        apply ugt_one
        rw [hsub, hx, uadd_toNat, ulit_toNat' 0 (by decide), hsw,
          Nat.add_zero, Nat.zero_mod]
        decide
      rw [h1']; decide
    have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_233_taken
      (by (try simp only [List.length_cons]); omega) h233 (by jump_dest) rd1
    exact tickLibWrapperBlocks.tickLibWrapper_block_280
      (by simp only [tickLibWrapperBlocks.tickLibWrapper_block_233_taken_stack,
        List.length_cons, List.length_nil]; omega) rd2
  · -- `s = 0`, `low ≥ 1`: `221`/`233` fall through, `446` sees the zero divisor → `456`.
    subst hs0
    have hlow' : low < UInt256.size :=
      lt_of_le_of_lt hlow (by decide : (6744:Nat) < UInt256.size)
    have hxT : x.toNat = low := by
      rw [hx, uadd_toNat, ulit_toNat' low hlow', hsw, Nat.add_zero,
        Nat.mod_eq_of_lt hlow']
    have h221 : UInt256.gt (UInt256.ofNat low) x = ⟨0⟩ := by
      apply ugt_zero
      rw [hxT, ulit_toNat' low hlow']
    have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_221_fallthrough
      (by (try simp only [List.length_cons]); omega) h221 rd
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_221_fallthrough_stack] at rd1
    have hsub : (x + UInt256.lnot ⟨0⟩).toNat = low - 1 := by
      rw [uadd_toNat, hxT, lnot_toNat_gen,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide]
      have hsz : UInt256.size = 2 ^ 256 := rfl
      rw [show low + (2 ^ 256 - 1 - 0) = low - 1 + UInt256.size from by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have h233 : UInt256.gt (x + UInt256.lnot ⟨0⟩) x = ⟨0⟩ := by
      apply ugt_zero
      rw [hsub, hxT]; omega
    have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_233_fallthrough
      (by (try simp only [List.length_cons]); omega) h233 rd1
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_233_fallthrough_stack] at rd2
    have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_244
      (by (try simp only [List.length_cons]); omega) (by jump_dest) rd2
    simp only [tickLibWrapperBlocks.tickLibWrapper_block_244_stack] at rd3
    have h446 : UInt256.isZero sw ≠ ⟨0⟩ := by
      have hz : sw = ⟨0⟩ := by
        apply u256_inj
        rw [hsw]; decide
      rw [hz]; decide
    have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_446_taken
      (by (try simp only [List.length_cons]); omega) h446 (by jump_dest) rd3
    exact tickLibWrapperBlocks.tickLibWrapper_block_456
      (by simp only [List.length_cons, List.length_nil]; omega) rd4

/-- The whole `priceToTick_body`, coupled: either the Stele body returns `pttResult lf s`
    for some final `lf` and the EVM run returns the same word, or both sides revert. -/
theorem p2tX_body {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ}
    (cfg : Config) (caller : Frame) (evm : EVM.State)
    (p s : Nat) (hp : p ≤ 1000000000000000000)
    (pw sw : UInt256) (hpw : pw.toNat = p) (hsw : sw.toNat = s)
    {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hcontract : caller.contract = contract)
    (hlp : caller.locals.get? "price" = some (.int (Int.ofNat p)))
    (hls : caller.locals.get? "spacing" = some (.int (Int.ofNat s)))
    (hmem : mem = (UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty
      (UInt256.ofNat 64).toNat 32)
    (rd : RD tickLibWrapperBytecode ee g s0 (UInt256.ofNat 213)
      (pw :: UInt256.ofNat 6744 :: ⟨0⟩ :: sw :: R) mem aw rdata σ k C) :
    (∃ (lf : Nat) (L' : Store),
      ExecFuncBody cfg caller evm priceToTickBodyDecl.body
        (.returned { caller with locals := L' } evm
          (some [.int (pttResult (Int.ofNat lf) (Int.ofNat s))])) ∧
      RDret tickLibWrapperBytecode g s0 σ
        (EVM.wordOfInt (pttResult (Int.ofNat lf) (Int.ofNat s))).toByteArray ∧
      lf ≤ 6744 ∧ 1 ≤ lf + s ∧ lf + s < UInt256.size ∧ s ≠ 0) ∨
    (ExecFuncBody cfg caller evm priceToTickBodyDecl.body .reverted ∧
      RDrev tickLibWrapperBytecode g s0) := by
  rw [p2tBodyDecl_body_eq]
  have hreq : evalExpr? cfg caller evm
      (.binary .le (.var "price") (.intLit 1000000000000000000)) = .ok (.bool true) := by
    simp only [evalExpr?, hlp, evalBinaryOp?, EvalResult.bind, bind, EvalResult.ofOption]
    rw [show decide (Int.ofNat p ≤ (1000000000000000000 : Int)) = true from
      decide_eq_true_iff.mpr (Int.ofNat_le.mpr hp)]
  have hlowEval : evalExpr? cfg caller evm (.intLit 0) = .ok (.int 0) := by
    simp only [evalExpr?, pure]
  have hhighEval : evalExpr? cfg
      { caller with locals := caller.locals.insert "low" (.int 0) } evm (.intLit 6744) =
      .ok (.int 6744) := by
    simp only [evalExpr?, pure]
  set L0 := (caller.locals.insert "low" (.int 0)).insert "high" (.int 6744) with hL0
  have hlow0 : L0.get? "low" = some (.int (Int.ofNat 0)) := by
    rw [hL0, store_get_ne _ (.int 6744) (by decide : ("high" == "low") = false)]
    exact store_get_self _ _ _
  have hhigh0 : L0.get? "high" = some (.int (Int.ofNat 6744)) := store_get_self _ _ _
  have hprice0 : L0.get? "price" = some (.int (Int.ofNat p)) := by
    rw [hL0, store_get_ne _ (.int 6744) (by decide : ("high" == "price") = false),
      store_get_ne _ (.int 0) (by decide : ("low" == "price") = false)]
    exact hlp
  have hsp0 : L0.get? "spacing" = some (.int (Int.ofNat s)) := by
    rw [hL0, store_get_ne _ (.int 6744) (by decide : ("high" == "spacing") = false),
      store_get_ne _ (.int 0) (by decide : ("low" == "spacing") = false)]
    exact hls
  have hchain := (ABlock.start.requireStep hreq).letStep (ty := none) hlowEval |>.letStep
    (name := "high") (ty := none) (rest :=
      [.while (.binary .ne (.var "low") (.var "high")) p2tLoopBodyStmts,
       .return [.binary .mul
         (.inRange uint256T
           (.binary .div
             (.inRange uint256T
               (.binary .sub
                 (.inRange uint256T
                   (.binary .add (.var "low") (.var "spacing")))
                 (.intLit 1)))
             (.var "spacing")))
         (.var "spacing")]]) hhighEval
  rcases p2tX_loop hstack p s hpw hsw hcontract 6744 0 6744 L0 k C
      hlow0 hhigh0 hprice0 hsp0 (by omega) (by omega) (by omega) rd with
    ⟨lf, L', k', C', hwhile, gl', gh', gp', gs', hlf, rd221⟩ | ⟨hwhile, hrev⟩
  · -- Stele-side exit tail (mirrors `p2tBodyStele`); EVM `221`-tail via `p2tX_tail_*`.
    have hWM : (Int.ofNat EVM.wordModulus : Int) = (2 : Int) ^ 256 := by decide
    have hsnn : (0 : Int) ≤ Int.ofNat s := Int.ofNat_nonneg _
    have haddE : evalExpr? cfg { caller with locals := L' } evm
        (.binary .add (.var "low") (.var "spacing")) =
        .ok (.int (Int.ofNat lf + Int.ofNat s)) := by
      simp only [evalExpr?, gl', gs', evalBinaryOp?, EvalResult.bind, bind,
        EvalResult.ofOption]
    have hnatSum : Int.ofNat lf + Int.ofNat s = Int.ofNat (lf + s) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    by_cases hov : Int.ofNat EVM.wordModulus ≤ Int.ofNat lf + Int.ofNat s
    · -- `(low + spacing) as uint256` overflows → both sides revert.
      right
      have hovN : UInt256.size ≤ lf + s := by
        rw [hnatSum] at hov
        have hle : Int.ofNat EVM.wordModulus ≤ Int.ofNat (lf + s) := hov
        have h := Int.ofNat_le.mp hle
        rwa [show EVM.wordModulus = UInt256.size from by decide] at h
      have hR1 : evalExpr? cfg { caller with locals := L' } evm
          (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) = .revert :=
        p2tInRange_rev haddE (Or.inr (hWM ▸ hov))
      have hmulR : evalExpr? cfg { caller with locals := L' } evm
          (.binary .mul
            (.inRange uint256T
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T
                      (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")))
            (.var "spacing")) = .revert := by
        simp only [evalExpr?, hR1, EvalResult.bind, bind]
      have hret : evalExprs? cfg { caller with locals := L' } evm
          [.binary .mul
            (.inRange uint256T
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T
                      (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")))
            (.var "spacing")] = .revert := by
        simp only [evalExprs?, hmulR, EvalResult.bind, bind]
      exact ⟨ExecFuncBody.execBlockRevert (hchain |>.run
          (ExecBlock.consNormal hwhile (ExecBlock.consRevert (ExecStmt.returnRevert hret)))),
        p2tX_tail_rev hstack hsw hlf (Or.inl hovN) rd221⟩
    · by_cases hzero : Int.ofNat lf + Int.ofNat s < 1
      · -- `low + spacing - 1 < 0`: the second `as uint256` reverts; EVM `233`-taken.
        right
        have hzN : lf + s = 0 := by
          rw [hnatSum] at hzero
          exact Nat.lt_one_iff.mp (Int.ofNat_lt.mp
            (show Int.ofNat (lf + s) < Int.ofNat 1 from hzero))
        have hR1 : evalExpr? cfg { caller with locals := L' } evm
            (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) =
            .ok (.int (Int.ofNat lf + Int.ofNat s)) :=
          p2tInRange_ok haddE
            (by rw [hnatSum]; exact not_lt.mpr (Int.ofNat_nonneg _))
            (by rw [hnatSum]; omega)
        have hsubE : evalExpr? cfg { caller with locals := L' } evm
            (.binary .sub
              (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
              (.intLit 1)) = .ok (.int (Int.ofNat lf + Int.ofNat s - 1)) := by
          simp only [evalExpr?, hR1, evalBinaryOp?, EvalResult.bind, bind,
            EvalResult.ofOption]
        have hR2 : evalExpr? cfg { caller with locals := L' } evm
            (.inRange uint256T
              (.binary .sub
                (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                (.intLit 1))) = .revert :=
          p2tInRange_rev hsubE (Or.inl (by omega))
        have hmulR : evalExpr? cfg { caller with locals := L' } evm
            (.binary .mul
              (.inRange uint256T
                (.binary .div
                  (.inRange uint256T
                    (.binary .sub
                      (.inRange uint256T
                        (.binary .add (.var "low") (.var "spacing")))
                      (.intLit 1)))
                  (.var "spacing")))
              (.var "spacing")) = .revert := by
          simp only [evalExpr?, hR2, EvalResult.bind, bind]
        have hret : evalExprs? cfg { caller with locals := L' } evm
            [.binary .mul
              (.inRange uint256T
                (.binary .div
                  (.inRange uint256T
                    (.binary .sub
                      (.inRange uint256T
                        (.binary .add (.var "low") (.var "spacing")))
                      (.intLit 1)))
                  (.var "spacing")))
              (.var "spacing")] = .revert := by
          simp only [evalExprs?, hmulR, EvalResult.bind, bind]
        exact ⟨ExecFuncBody.execBlockRevert (hchain |>.run
            (ExecBlock.consNormal hwhile
              (ExecBlock.consRevert (ExecStmt.returnRevert hret)))),
          p2tX_tail_rev hstack hsw hlf (Or.inr (Or.inl hzN)) rd221⟩
      · by_cases hs0 : Int.ofNat s = 0
        · -- `spacing = 0`: the `/` reverts on both sides (`446`-taken → `456`).
          right
          have hs0N : s = 0 :=
            Int.ofNat_inj.mp (show Int.ofNat s = Int.ofNat 0 from hs0)
          have h1N : 1 ≤ lf + s := by
            rw [hnatSum] at hzero
            exact Int.ofNat_le.mp (le_of_not_gt hzero)
          have hR1 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) =
              .ok (.int (Int.ofNat lf + Int.ofNat s)) :=
            p2tInRange_ok haddE
            (by rw [hnatSum]; exact not_lt.mpr (Int.ofNat_nonneg _))
            (by rw [hnatSum]; omega)
          have hsubE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .sub
                (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                (.intLit 1)) = .ok (.int (Int.ofNat lf + Int.ofNat s - 1)) := by
            simp only [evalExpr?, hR1, evalBinaryOp?, EvalResult.bind, bind,
              EvalResult.ofOption]
          have hR2 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T
                (.binary .sub
                  (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                  (.intLit 1))) = .ok (.int (Int.ofNat lf + Int.ofNat s - 1)) :=
            p2tInRange_ok hsubE (by omega) (by omega)
          have hspE : evalExpr? cfg { caller with locals := L' } evm (.var "spacing") =
              .ok (.int (Int.ofNat s)) := by
            simp only [evalExpr?, gs', EvalResult.ofOption]
          have hdivR : evalExpr? cfg { caller with locals := L' } evm
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")) = .revert := by
            simp only [evalExpr?, hR2, hspE, evalBinaryOp?, EvalResult.bind, bind,
              hs0]
            rfl
          have hmulR : evalExpr? cfg { caller with locals := L' } evm
              (.binary .mul
                (.inRange uint256T
                  (.binary .div
                    (.inRange uint256T
                      (.binary .sub
                        (.inRange uint256T
                          (.binary .add (.var "low") (.var "spacing")))
                        (.intLit 1)))
                    (.var "spacing")))
                (.var "spacing")) = .revert := by
            simp only [evalExpr?, hdivR, EvalResult.bind, bind]
          have hret : evalExprs? cfg { caller with locals := L' } evm
              [.binary .mul
                (.inRange uint256T
                  (.binary .div
                    (.inRange uint256T
                      (.binary .sub
                        (.inRange uint256T
                          (.binary .add (.var "low") (.var "spacing")))
                        (.intLit 1)))
                    (.var "spacing")))
                (.var "spacing")] = .revert := by
            simp only [evalExprs?, hmulR, EvalResult.bind, bind]
          exact ⟨ExecFuncBody.execBlockRevert (hchain |>.run
              (ExecBlock.consNormal hwhile
                (ExecBlock.consRevert (ExecStmt.returnRevert hret)))),
            p2tX_tail_rev hstack hsw hlf (Or.inr (Or.inr ⟨hs0N, h1N⟩)) rd221⟩
        · -- all guards pass: Stele returns `pttResult lf s`, EVM returns the same word.
          left
          have hsN : s ≠ 0 := by
            intro h; apply hs0; rw [h]; rfl
          have h1N : 1 ≤ lf + s := by
            rw [hnatSum] at hzero
            exact Int.ofNat_le.mp (le_of_not_gt hzero)
          have hovN : lf + s < UInt256.size := by
            rw [hnatSum] at hov
            rw [show Int.ofNat EVM.wordModulus = Int.ofNat UInt256.size from
              by decide] at hov
            exact Nat.lt_of_not_le (fun hc => hov (Int.ofNat_le.mpr hc))
          have hR1 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T (.binary .add (.var "low") (.var "spacing"))) =
              .ok (.int (Int.ofNat lf + Int.ofNat s)) :=
            p2tInRange_ok haddE
            (by rw [hnatSum]; exact not_lt.mpr (Int.ofNat_nonneg _))
            (by rw [hnatSum]; omega)
          have hsubE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .sub
                (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                (.intLit 1)) = .ok (.int (Int.ofNat lf + Int.ofNat s - 1)) := by
            simp only [evalExpr?, hR1, evalBinaryOp?, EvalResult.bind, bind,
              EvalResult.ofOption]
          have hR2 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T
                (.binary .sub
                  (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                  (.intLit 1))) = .ok (.int (Int.ofNat lf + Int.ofNat s - 1)) :=
            p2tInRange_ok hsubE (by omega) (by omega)
          have hspE : evalExpr? cfg { caller with locals := L' } evm (.var "spacing") =
              .ok (.int (Int.ofNat s)) := by
            simp only [evalExpr?, gs', EvalResult.ofOption]
          have hdivE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .div
                (.inRange uint256T
                  (.binary .sub
                    (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                    (.intLit 1)))
                (.var "spacing")) = .ok (.int ((Int.ofNat lf + Int.ofNat s - 1)
                  / Int.ofNat s)) := by
            simp only [evalExpr?, hR2, hspE, evalBinaryOp?, EvalResult.bind, bind, hs0]
            rfl
          have hR3 : evalExpr? cfg { caller with locals := L' } evm
              (.inRange uint256T
                (.binary .div
                  (.inRange uint256T
                    (.binary .sub
                      (.inRange uint256T (.binary .add (.var "low") (.var "spacing")))
                      (.intLit 1)))
                  (.var "spacing"))) =
              .ok (.int ((Int.ofNat lf + Int.ofNat s - 1) / Int.ofNat s)) := by
            have hnn : 0 ≤ Int.ofNat lf + Int.ofNat s - 1 := by omega
            have hnn2 : 0 ≤ (Int.ofNat lf + Int.ofNat s - 1) / Int.ofNat s :=
              Int.ediv_nonneg hnn hsnn
            have hle2 : (Int.ofNat lf + Int.ofNat s - 1) / Int.ofNat s ≤
                Int.ofNat lf + Int.ofNat s - 1 := Int.ediv_le_self _ hnn
            exact p2tInRange_ok hdivE (by omega) (by omega)
          have hmulE : evalExpr? cfg { caller with locals := L' } evm
              (.binary .mul
                (.inRange uint256T
                  (.binary .div
                    (.inRange uint256T
                      (.binary .sub
                        (.inRange uint256T
                          (.binary .add (.var "low") (.var "spacing")))
                        (.intLit 1)))
                    (.var "spacing")))
                (.var "spacing")) =
              .ok (.int (pttResult (Int.ofNat lf) (Int.ofNat s))) := by
            simp only [evalExpr?, hR3, hspE, evalBinaryOp?, EvalResult.bind, bind,
              pttResult]
          refine ⟨lf, L',
            ExecFuncBody.execBlockRet ((hchain).whileStep hwhile |>.returns hmulE),
            ?_, hlf, h1N, hovN, hsN⟩
          exact p2tX_tail_ok hstack hsw hmem hovN h1N hsN rd221
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (hchain |>.run
      (ExecBlock.consRevert hwhile)), hrev⟩

/-- `priceToTick(uint256,uint256)`'s transition body as emitted. -/
theorem priceToTickBody_eq : priceToTickTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "__calldata" (some .bytes) (.env .msgData),
     .require (.binary .lt
        (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)),
     .internalCall "priceToTick_body" [.var "price", .var "spacing"] "__r",
     .return [.var "__r"]] := rfl

/-- `priceToTick(uint256,uint256)`'s spec body returns `some [.int (pttResult lf s)]`
    whenever the callee body does. -/
theorem p2tTransitionReturns (evm : EVM.State) (p s lf : Nat) (callargs : Store) (stele' : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hb : ExecFuncBody config
      { contract := contract,
        locals := ((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert "price"
          (.int (Int.ofNat p)), immutables := ∅ }
      evm priceToTickBodyDecl.body
      (.returned stele' evm (some [.int (pttResult (Int.ofNat lf) (Int.ofNat s))])))
    (hx1 : callargs.get? "price" = some (.int (Int.ofNat p)))
    (hx2 : callargs.get? "spacing" = some (.int (Int.ofNat s))) :
    ∃ cs, ExecTransitionBody config contract evm callargs priceToTickTransition.body
      (.returned cs evm (some [.int (pttResult (Int.ofNat lf) (Int.ofNat s))])) := by
  rw [priceToTickBody_eq]
  let cd : ByteArray := evm.executionEnv.calldata
  have hx1' : (callargs.insert "__calldata" (.bytes cd)).get? "price" =
      some (.int (Int.ofNat p)) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "price") = false)]
    exact hx1
  have hx2' : (callargs.insert "__calldata" (.bytes cd)).get? "spacing" =
      some (.int (Int.ofNat s)) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "spacing") = false)]
    exact hx2
  have hargs : evalExprs? config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } evm
      [.var "price", .var "spacing"] =
      .ok [.int (Int.ofNat p), .int (Int.ofNat s)] := by
    simp only [evalExprs?, evalExpr?, hx1', hx2', EvalResult.bind, bind,
      EvalResult.ofOption, pure]
  have hlookup : lookupCallable? contract "priceToTick_body" =
      some priceToTickBodyDecl.toCallable := rfl
  have hbind : bindParams? priceToTickBodyDecl.params
      [.int (Int.ofNat p), .int (Int.ofNat s)] =
      some (((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert "price"
        (.int (Int.ofNat p))) := rfl
  have hic := internalCallFunctionReturn (name := "priceToTick_body") (retVar := "__r")
      (args := [.var "price", .var "spacing"])
      (argVals := [.int (Int.ofNat p), .int (Int.ofNat s)])
      (locals := ((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert "price"
        (.int (Int.ofNat p)))
      (callee := priceToTickBodyDecl) hargs hlookup hbind hb
  let resumed : Frame := resumeAfterInternalCall
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } "__r"
      (some [.int (pttResult (Int.ofNat lf) (Int.ofNat s))])
  have hres : resumed.locals.get? "__r" =
      some (.int (pttResult (Int.ofNat lf) (Int.ofNat s))) := by
    show ((callargs.insert "__calldata" (.bytes cd)).insert "__r"
        (collapseReturns [.int (pttResult (Int.ofNat lf) (Int.ofNat s))])).get? "__r" = _
    rw [show collapseReturns [.int (pttResult (Int.ofNat lf) (Int.ofNat s))] =
      .int (pttResult (Int.ofNat lf) (Int.ofNat s)) from rfl]
    exact store_get_self _ _ _
  have hret : evalExpr? config resumed evm (.var "__r") =
      .ok (.int (pttResult (Int.ofNat lf) (Int.ofNat s))) := by
    simp only [evalExpr?, hres, EvalResult.bind, bind, EvalResult.ofOption, pure]
  refine ⟨⟨contract, resumed.locals, ∅⟩, ExecFuncBody.execBlockRet ?_⟩
  have blk : ExecBlock config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ }
      evm [Stmt.internalCall "priceToTick_body" [.var "price", .var "spacing"] "__r",
           Stmt.return [.var "__r"]]
      (.returned resumed evm
        (some [.int (pttResult (Int.ofNat lf) (Int.ofNat s))])) :=
    ExecBlock.consNormal hic
      (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret)))
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireStep
      (evalCalldataLen_true (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen) |>.run blk

/-- `priceToTick(uint256,uint256)`'s spec body reverts whenever the callee body does. -/
theorem p2tTransitionReverts_call (evm : EVM.State) (p s : Nat) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrev : ExecFuncBody config
      { contract := contract,
        locals := ((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert "price"
          (.int (Int.ofNat p)), immutables := ∅ }
      evm priceToTickBodyDecl.body .reverted)
    (hx1 : callargs.get? "price" = some (.int (Int.ofNat p)))
    (hx2 : callargs.get? "spacing" = some (.int (Int.ofNat s))) :
    ExecTransitionBody config contract evm callargs priceToTickTransition.body
      .reverted := by
  rw [priceToTickBody_eq]
  let cd : ByteArray := evm.executionEnv.calldata
  have hx1' : (callargs.insert "__calldata" (.bytes cd)).get? "price" =
      some (.int (Int.ofNat p)) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "price") = false)]
    exact hx1
  have hx2' : (callargs.insert "__calldata" (.bytes cd)).get? "spacing" =
      some (.int (Int.ofNat s)) := by
    rw [store_get_ne _ (.bytes cd) (by decide : ("__calldata" == "spacing") = false)]
    exact hx2
  have hargs : evalExprs? config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ } evm
      [.var "price", .var "spacing"] =
      .ok [.int (Int.ofNat p), .int (Int.ofNat s)] := by
    simp only [evalExprs?, evalExpr?, hx1', hx2', EvalResult.bind, bind,
      EvalResult.ofOption, pure]
  have hlookup : lookupCallable? contract "priceToTick_body" =
      some priceToTickBodyDecl.toCallable := rfl
  have hbind : bindParams? priceToTickBodyDecl.params
      [.int (Int.ofNat p), .int (Int.ofNat s)] =
      some (((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert "price"
        (.int (Int.ofNat p))) := rfl
  have hic := internalCallFunctionRevert (name := "priceToTick_body") (retVar := "__r")
      (args := [.var "price", .var "spacing"])
      (argVals := [.int (Int.ofNat p), .int (Int.ofNat s)])
      (locals := ((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert "price"
        (.int (Int.ofNat p)))
      (callee := priceToTickBodyDecl) hargs hlookup hbind hrev
  refine ExecFuncBody.execBlockRevert ?_
  have blk : ExecBlock config
      { contract := contract,
        locals := callargs.insert "__calldata" (.bytes cd), immutables := ∅ }
      evm [Stmt.internalCall "priceToTick_body" [.var "price", .var "spacing"] "__r",
           Stmt.return [.var "__r"]]
      .reverted := ExecBlock.consRevert hic
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireStep
      (evalCalldataLen_true (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen) |>.run blk

/-- `priceToTick(uint256,uint256)`'s spec body reverts at the calldata-size require when
    the calldata is too large to be decoded. -/
theorem p2tTransitionReverts_len (evm : EVM.State) (callargs : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : 2 ^ 255 + 4 ≤ evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm callargs priceToTickTransition.body
      .reverted := by
  rw [priceToTickBody_eq]
  refine ExecFuncBody.execBlockRevert ?_
  exact (ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep
      (by simp only [evalExpr?, envValue, pure]) |>.requireRevert
      (evalCalldataLen_false (store_get_self _ "__calldata"
        (.bytes evm.executionEnv.calldata)) hlen)

/-- `wordOfInt (pttResult lf s)` transports back to `pttResult lf s` through `toNat`
    whenever the tail guards passed (`1 ≤ lf + s`, `s ≠ 0`, `lf + s < 2^256`). -/
theorem pttResult_toNat (lf s : Nat)
    (h1 : 1 ≤ lf + s) (hs : s ≠ 0) (hb : lf + s < UInt256.size) :
    Int.ofNat (EVM.wordOfInt (pttResult (Int.ofNat lf) (Int.ofNat s))).toNat =
      pttResult (Int.ofNat lf) (Int.ofNat s) := by
  have hsI : (0 : Int) < (s : Int) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hs)
  have hsum' : Int.ofNat lf + Int.ofNat s = Int.ofNat (lf + s) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
  have hnn : 0 ≤ pttResult (Int.ofNat lf) (Int.ofNat s) := by
    show 0 ≤ ((Int.ofNat lf + Int.ofNat s - 1) / Int.ofNat s) * Int.ofNat s
    have hnum : 0 ≤ Int.ofNat lf + Int.ofNat s - 1 := by
      rw [hsum']
      exact Int.sub_nonneg.mpr (show (1 : Int) ≤ Int.ofNat (lf + s) from
        Int.ofNat_le.mpr h1)
    exact Int.mul_nonneg
      (Int.ediv_nonneg hnum (Int.ofNat_nonneg _)) (Int.ofNat_nonneg _)
  have hle : pttResult (Int.ofNat lf) (Int.ofNat s) ≤ Int.ofNat lf + Int.ofNat s - 1 := by
    show ((Int.ofNat lf + Int.ofNat s - 1) / Int.ofNat s) * Int.ofNat s ≤
      Int.ofNat lf + Int.ofNat s - 1
    exact Int.ediv_mul_le _ (ne_of_gt hsI)
  have hltm : pttResult (Int.ofNat lf) (Int.ofNat s) < Int.ofNat EVM.wordModulus := by
    rw [show Int.ofNat EVM.wordModulus = Int.ofNat UInt256.size from by decide]
    exact lt_of_le_of_lt hle (by
      rw [hsum']
      exact lt_trans (Int.sub_lt_self _ (by decide : (0:Int) < 1))
        (Int.ofNat_lt.mpr hb))
  rw [wordOfInt_toNat, Int.emod_eq_of_lt hnn hltm]
  exact Int.toNat_of_nonneg hnn

/-- `priceToTick(uint256,uint256)` — the EVM arm through the binary-search body agrees
    with the dispatched Stele transition on every outcome. -/
theorem tickLibWrapperPriceToTickBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = tickLibWrapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (tickLibWrapperSelBytes 3)
    rfl hsel
  have h0 : ¬ selIs I (tickLibWrapperSelBytes 0) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h1 : ¬ selIs I (tickLibWrapperSelBytes 1) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have h2 : ¬ selIs I (tickLibWrapperSelBytes 2) := by
    intro h
    exact absurd ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm) (by decide)
  have hd : dispatchMsg contract I.calldata = some priceToTickTransition :=
    tickLibWrapperDispatch_priceToTick h0 h1 h2 hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases h68 : 68 ≤ I.calldata.size
      · -- `68 ≤ size < 2^255 + 4`: decode succeeds, run the body.
        have hdec := p2tDecode_ok h68 hbig
        set p := (calldataWord I.calldata 4).toNat with hp
        set s := (calldataWord I.calldata 36).toNat with hs
        set pw : UInt256 := uInt256OfByteArray
          (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) with hpw
        set sw : UInt256 := uInt256OfByteArray
          (I.calldata.readBytes (UInt256.ofNat 36).toNat 32) with hsw
        have hpwt : pw.toNat = p := by
          rw [hpw, hp, calldataWord,
            show (UInt256.ofNat 4).toNat = 4 from by decide]
        have hswt : sw.toNat = s := by
          rw [hsw, hs, calldataWord,
            show (UInt256.ofNat 36).toNat = 36 from by decide]
        by_cases hle : p ≤ 1000000000000000000
        · -- decoded `price ≤ 1e18`: the arm runs the loop.
          obtain ⟨_, _, rd⟩ := tickLibWrapperReachPriceToTickBody (σ := σ) (σ₀ := σ₀)
            (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
          have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_168_fallthrough
            (by simp) hwv rd
          have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size)
              ⟨64⟩ = ⟨0⟩ := by
            rw [lnot3_add_returnSize hsz hsize]
            show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 64) =
              ⟨0⟩
            exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
          have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_174_fallthrough
            (by simp) hslt rd1
          have hgt' : UInt256.gt (uInt256OfByteArray
              (I.calldata.readBytes (UInt256.ofNat 4).toNat 32))
              (UInt256.ofNat 1000000000000000000) = ⟨0⟩ := by
            apply ugt_zero
            rw [ulit_toNat' _ (by decide : (1000000000000000000 : Nat) < UInt256.size)]
            have hw : (uInt256OfByteArray
                (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toNat =
                (calldataWord I.calldata 4).toNat := rfl
            rw [hw, ← hp]
            exact hle
          have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_186_fallthrough
            (by simp) hgt' rd2
          simp only [tickLibWrapperBlocks.tickLibWrapper_block_186_fallthrough_stack]
            at rd3
          have rd4 := tickLibWrapperBlocks.tickLibWrapper_block_207
            (by simp only [List.length_cons, List.length_nil]; omega) rd3
          simp only [tickLibWrapperBlocks.tickLibWrapper_block_207_stack] at rd4
          have hpriceB : (((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert
              "price" (.int (Int.ofNat p))).get? "price" =
              some (.int (Int.ofNat p)) := store_get_self _ _ _
          have hspacingB : (((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert
              "price" (.int (Int.ofNat p))).get? "spacing" =
              some (.int (Int.ofNat s)) := by
            rw [store_get_ne _ _
              (by decide : ("price" == "spacing") = false)]
            exact store_get_self _ _ _
          have hx1B : (((∅ : Store).insert "price" (.int (Int.ofNat p))).insert
              "spacing" (.int (Int.ofNat s))).get? "price" =
              some (.int (Int.ofNat p)) := by
            rw [store_get_ne _ _
              (by decide : ("spacing" == "price") = false)]
            exact store_get_self _ _ _
          have hx2B : (((∅ : Store).insert "price" (.int (Int.ofNat p))).insert
              "spacing" (.int (Int.ofNat s))).get? "spacing" =
              some (.int (Int.ofNat s)) := store_get_self _ _ _
          rcases p2tX_body config
              { contract := contract,
                locals := ((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert
                  "price" (.int (Int.ofNat p)), immutables := ∅ }
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) p s hle pw sw hpwt hswt
              (by simp only [List.length_cons, List.length_nil]; omega) rfl
              hpriceB hspacingB rfl rd4 with
            ⟨lf, L', hbody, hret, hlf, h1N, hovN, hsN⟩ | ⟨hbody, hrev⟩
          · obtain ⟨cs, hb⟩ := p2tTransitionReturns
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) p s lf
              (((∅ : Store).insert "price" (.int (Int.ofNat p))).insert "spacing"
                (.int (Int.ofNat s))) _
              (by simp only [initState]; exact hwv)
              (by simp only [initState]; exact hbig)
              hbody hx1B hx2B
            exact hret.reEquivExecution hcode hd hdec hb
              (returnEquiv_of_encode (by
                have henc := uint256ReturnEncoding
                  (EVM.wordOfInt (pttResult (Int.ofNat lf) (Int.ofNat s)))
                rw [pttResult_toNat lf s h1N hsN hovN] at henc
                exact henc))
          · have hbody' : ExecTransitionBody config contract
                (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (((∅ : Store).insert "price" (.int (Int.ofNat p))).insert "spacing"
                  (.int (Int.ofNat s)))
                priceToTickTransition.body .reverted :=
              p2tTransitionReverts_call
                (initState σ σ₀ (Sat256.ofUInt256 g) A I) p s _
                (by simp only [initState]; exact hwv)
                (by simp only [initState]; exact hbig)
                hbody hx1B hx2B
            exact hrev.reEquivExecutionRevert hcode hd hdec hbody'
        · -- `price > 1e18`: spec `require` reverts; EVM `186 → 344`.
          have hgt : 1000000000000000000 < (calldataWord I.calldata 4).toNat := by
            rw [← hp]; omega
          have hbody : ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (((∅ : Store).insert "price" (.int (Int.ofNat p))).insert "spacing"
                (.int (Int.ofNat s)))
              priceToTickTransition.body .reverted :=
            p2tTransitionReverts_call
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) p s _
              (by simp only [initState]; exact hwv)
              (by simp only [initState]; exact hbig)
              (p2tBodyStele_req config
                { contract := contract,
                  locals := ((∅ : Store).insert "spacing" (.int (Int.ofNat s))).insert
                    "price" (.int (Int.ofNat p)), immutables := ∅ }
                _ p hle (store_get_self _ _ _))
              (by
                have hne : ("spacing" == "price") = false := by decide
                rw [store_get_ne _ _ hne]
                exact store_get_self _ _ _)
              (store_get_self _ _ _)
          exact (p2tX_rev_gate (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig h68
              hsel hgt)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · -- `4 ≤ size < 68`: decode fails (not enough args bytes) → revert at 131.
        have hdec : config.externalABI.decodeCalldata?
            (priceToTickTransition.params.map Param.name)
            (transitionSignature priceToTickTransition).paramTypes I.calldata = none :=
          p2tDecode_none hsz (Or.inl (by omega))
        have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
          p2tX_rev hcode hwv hsz hsize (Or.inl (by omega)) hsel
        rcases hrd with hOOG | ⟨g', o, hrev⟩
        · rw [← hcode] at hOOG
          exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
            simpa [Sat256.ofUInt256_toNat] using hOOG))
        · rw [← hcode] at hrev
          exact reEquiv_decodingFailed hd hdec (Xi_revert_of_X (g := g) (by
            simpa [Sat256.ofUInt256_toNat] using hrev))
    · -- `size ≥ 2^255 + 4`: decode fails (huge args) → revert at 131.
      have hdec : config.externalABI.decodeCalldata?
          (priceToTickTransition.params.map Param.name)
          (transitionSignature priceToTickTransition).paramTypes I.calldata = none :=
        p2tDecode_none hsz (Or.inr (by omega))
      have hrd : RDrev tickLibWrapperBytecode (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) :=
        p2tX_rev hcode hwv hsz hsize (Or.inr (by omega)) hsel
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
      p2tX_revert_pay hcode hwv hsz hsize hsel
    rcases hrd with hOOG | ⟨g', o, hrev⟩
    · rw [← hcode] at hOOG
      exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
        simpa [Sat256.ofUInt256_toNat] using hOOG))
    · rw [← hcode] at hrev
      have hΞ : Ξ σ σ₀ g A I = .ok (.revert g' o) :=
        Xi_revert_of_X (g := g) (by simpa [Sat256.ofUInt256_toNat] using hrev)
      by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases h68 : 68 ≤ I.calldata.size
        · have hdec := p2tDecode_ok h68 hbig
          have hbody : ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (((∅ : Store).insert "price"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat))).insert "spacing"
                (.int (Int.ofNat (calldataWord I.calldata 36).toNat)))
              priceToTickTransition.body .reverted := by
            rw [priceToTickBody_eq]
            exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)
          exact reEquiv_execution hd hdec hbody (execResultsEquiv.revert hΞ rfl)
        · have hdec : config.externalABI.decodeCalldata?
              (priceToTickTransition.params.map Param.name)
              (transitionSignature priceToTickTransition).paramTypes I.calldata = none :=
            p2tDecode_none hsz (Or.inl (by omega))
          exact reEquiv_decodingFailed hd hdec hΞ
      · have hdec : config.externalABI.decodeCalldata?
            (priceToTickTransition.params.map Param.name)
            (transitionSignature priceToTickTransition).paramTypes I.calldata = none :=
          p2tDecode_none hsz (Or.inr (by omega))
        exact reEquiv_decodingFailed hd hdec hΞ

end Benchmarks.Midnight.TickLibWrapper
