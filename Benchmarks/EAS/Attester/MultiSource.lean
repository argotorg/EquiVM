import Benchmarks.EAS.Attester.InnerArrayEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def attesterRevocationDataValue (uid : Value) : Value :=
  .tuple [uid, .int 0]

def attesterRevocationDataValues : List Value → List Value
  | [] => []
  | uid :: rest => attesterRevocationDataValue uid :: attesterRevocationDataValues rest

def attesterRevocationDataDefault : Value :=
  attesterRevocationDataValue (.fixedBytes bytes32Width (List.replicate 32 0))

/-- Source-side shape of the inner `data` array after the first `n` entries have been filled. -/
def attesterRevocationDataPrefix : Nat → List Value → List Value
  | _, [] => []
  | 0, _ :: rest =>
      attesterRevocationDataDefault :: attesterRevocationDataPrefix 0 rest
  | n + 1, uid :: rest =>
      attesterRevocationDataValue uid :: attesterRevocationDataPrefix n rest

theorem attesterRevocationDataPrefix_length (n : Nat) (uids : List Value) :
    (attesterRevocationDataPrefix n uids).length = uids.length := by
  induction uids generalizing n with
  | nil =>
      cases n <;> simp [attesterRevocationDataPrefix]
  | cons _ rest ih =>
      cases n <;> simp [attesterRevocationDataPrefix, ih]

theorem attesterRevocationDataPrefix_zero (uids : List Value) :
    attesterRevocationDataPrefix 0 uids =
      List.replicate uids.length attesterRevocationDataDefault := by
  induction uids with
  | nil => simp [attesterRevocationDataPrefix]
  | cons _ rest ih =>
      change attesterRevocationDataDefault :: attesterRevocationDataPrefix 0 rest =
        List.replicate (rest.length + 1) attesterRevocationDataDefault
      rw [ih]
      rw [show (rest.length + 1) = Nat.succ rest.length by omega]
      rfl

theorem attesterRevocationDataPrefix_all (uids : List Value) :
    attesterRevocationDataPrefix uids.length uids =
      attesterRevocationDataValues uids := by
  induction uids with
  | nil => simp [attesterRevocationDataPrefix, attesterRevocationDataValues]
  | cons _ rest ih => simp [attesterRevocationDataPrefix, attesterRevocationDataValues, ih]

theorem attesterRevocationDataPrefix_update :
    ∀ {uids : List Value} {n : Nat}, n < uids.length →
      ∃ uid,
        lookupNth? uids n = some uid ∧
        updateNth? (attesterRevocationDataPrefix n uids) n
            (attesterRevocationDataValue uid) =
          some (attesterRevocationDataPrefix (n + 1) uids)
  | [], _, h => by simp at h
  | uid :: _, 0, _ => by
      exact ⟨uid, rfl, by simp [attesterRevocationDataPrefix, updateNth?]⟩
  | _ :: rest, n + 1, h => by
      have hlt : n < rest.length := by
        simpa using Nat.succ_lt_succ_iff.mp h
      obtain ⟨uid, hlookup, hupdate⟩ :=
        attesterRevocationDataPrefix_update (uids := rest) (n := n) hlt
      refine ⟨uid, ?_, ?_⟩
      · simpa [lookupNth?] using hlookup
      · simp [attesterRevocationDataPrefix, updateNth?, hupdate]

def attesterMultiRevokeRequestValue (schema : Value) (uids : List Value) : Value :=
  .tuple [schema, .array (attesterRevocationDataValues uids)]

def attesterMultiRevokeRequestDefault : Value :=
  .tuple [.fixedBytes bytes32Width (List.replicate 32 0), .array []]

def attesterMultiRevokeRequestValues : List Value → List Value → List Value
  | schema :: schemas, .array uids :: uidss =>
      attesterMultiRevokeRequestValue schema uids ::
        attesterMultiRevokeRequestValues schemas uidss
  | _, _ => []

/-- Source-side shape of `multiRequests` after the first `n` outer entries have been filled. -/
def attesterMultiRevokeRequestValuesPrefix : Nat → List Value → List Value → List Value
  | _, [], _ => []
  | 0, _ :: schemas, [] =>
      attesterMultiRevokeRequestDefault ::
        attesterMultiRevokeRequestValuesPrefix 0 schemas []
  | 0, _ :: schemas, _ :: schemaUids =>
      attesterMultiRevokeRequestDefault ::
        attesterMultiRevokeRequestValuesPrefix 0 schemas schemaUids
  | n + 1, schema :: schemas, .array uids :: schemaUids =>
      attesterMultiRevokeRequestValue schema uids ::
        attesterMultiRevokeRequestValuesPrefix n schemas schemaUids
  | n + 1, _ :: schemas, _ :: schemaUids =>
      attesterMultiRevokeRequestDefault ::
        attesterMultiRevokeRequestValuesPrefix n schemas schemaUids
  | n + 1, _ :: schemas, [] =>
      attesterMultiRevokeRequestDefault ::
        attesterMultiRevokeRequestValuesPrefix n schemas []

theorem attesterMultiRevokeRequestValuesPrefix_length
    (n : Nat) (schemas schemaUids : List Value) :
    (attesterMultiRevokeRequestValuesPrefix n schemas schemaUids).length =
      schemas.length := by
  induction schemas generalizing n schemaUids with
  | nil =>
      cases n <;> cases schemaUids <;>
        simp [attesterMultiRevokeRequestValuesPrefix]
  | cons _ schemas ih =>
      cases n <;> cases schemaUids with
      | nil =>
          simp [attesterMultiRevokeRequestValuesPrefix, ih]
      | cons head tail =>
          cases head <;>
            simp [attesterMultiRevokeRequestValuesPrefix, ih]

theorem attesterMultiRevokeRequestValuesPrefix_zero
    (schemas schemaUids : List Value) :
    attesterMultiRevokeRequestValuesPrefix 0 schemas schemaUids =
      List.replicate schemas.length attesterMultiRevokeRequestDefault := by
  induction schemas generalizing schemaUids with
  | nil =>
      cases schemaUids <;> simp [attesterMultiRevokeRequestValuesPrefix]
  | cons _ schemas ih =>
      cases schemaUids <;>
        change attesterMultiRevokeRequestDefault ::
            attesterMultiRevokeRequestValuesPrefix 0 schemas _ =
          List.replicate (schemas.length + 1) attesterMultiRevokeRequestDefault
      all_goals
        rw [ih]
        rw [show schemas.length + 1 = Nat.succ schemas.length by omega]
        rfl

theorem attesterMultiRevokeRequestValuesPrefix_update :
    ∀ {schemas schemaUids : List Value} {n : Nat} {schema : Value} {uids : List Value},
      lookupNth? schemas n = some schema →
      lookupNth? schemaUids n = some (.array uids) →
      updateNth? (attesterMultiRevokeRequestValuesPrefix n schemas schemaUids)
          n (attesterMultiRevokeRequestValue schema uids) =
        some (attesterMultiRevokeRequestValuesPrefix (n + 1) schemas schemaUids)
  | [], _, _, _, _, hschema, _ => by simp [lookupNth?] at hschema
  | _ :: _, [], 0, _, _, _, huids => by simp [lookupNth?] at huids
  | _ :: _, _ :: _, 0, _, _, hschema, huids => by
      simp [lookupNth?] at hschema huids
      cases hschema
      cases huids
      simp [attesterMultiRevokeRequestValuesPrefix, updateNth?]
  | _ :: schemas, head :: schemaUids, n + 1, schema, uids, hschema, huids => by
      have hschemaTail : lookupNth? schemas n = some schema := by
        simpa [lookupNth?] using hschema
      have huidsTail : lookupNth? schemaUids n = some (.array uids) := by
        simpa [lookupNth?] using huids
      have htail :=
        attesterMultiRevokeRequestValuesPrefix_update
          (schemas := schemas) (schemaUids := schemaUids) (n := n)
          (schema := schema) (uids := uids) hschemaTail huidsTail
      cases head <;>
        simp [attesterMultiRevokeRequestValuesPrefix, updateNth?, htail]
  | _ :: schemas, [], n + 1, _, _, _, huids => by
      simp [lookupNth?] at huids

theorem attesterMultiRevokeRequestValuesPrefix_all :
    ∀ {schemas schemaUids : List Value},
      schemaUids.length = schemas.length →
      (∀ {idx value}, lookupNth? schemaUids idx = some value →
        ∃ uids, value = .array uids) →
      attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids =
        attesterMultiRevokeRequestValues schemas schemaUids
  | [], [], _hlen, _hshape => by
      simp [attesterMultiRevokeRequestValuesPrefix, attesterMultiRevokeRequestValues]
  | [], _ :: _, hlen, _hshape => by
      simp at hlen
  | _ :: _, [], hlen, _hshape => by
      simp at hlen
  | schema :: schemas, value :: schemaUids, hlen, hshape => by
      have htailLen : schemaUids.length = schemas.length := by
        simp at hlen
        exact hlen
      obtain ⟨uids, hvalue⟩ := hshape (idx := 0) (value := value) (by rfl)
      subst value
      have htailShape :
          ∀ {idx value}, lookupNth? schemaUids idx = some value →
            ∃ uids, value = .array uids := by
        intro idx value hlookup
        exact hshape (idx := idx + 1) (value := value) (by
          simpa [lookupNth?] using hlookup)
      simp [attesterMultiRevokeRequestValuesPrefix, attesterMultiRevokeRequestValues,
        attesterMultiRevokeRequestValuesPrefix_all htailLen htailShape]

def attesterMultiRevokeRequestsValue (schemas schemaUids : List Value) : Value :=
  .array (attesterMultiRevokeRequestValues schemas schemaUids)

theorem attesterEvalAndTrue {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr}
    (hleft : evalExpr? cfg solm evm lhs = .ok (.bool true))
    (hright : evalExpr? cfg solm evm rhs = .ok (.bool true)) :
    evalExpr? cfg solm evm (.binary .and lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem attesterEvalBinaryEq {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {v₁ v₂ value : Value}
    (hleft : evalExpr? cfg solm evm lhs = .ok v₁)
    (hright : evalExpr? cfg solm evm rhs = .ok v₂)
    (hop : evalBinaryOp? .eq v₁ v₂ = .ok value) :
    evalExpr? cfg solm evm (.binary .eq lhs rhs) = .ok value := by
  simp [evalExpr?, hleft, hright, hop, EvalResult.bind, bind]

theorem attesterEvalBinaryLt {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {v₁ v₂ value : Value}
    (hleft : evalExpr? cfg solm evm lhs = .ok v₁)
    (hright : evalExpr? cfg solm evm rhs = .ok v₂)
    (hop : evalBinaryOp? .lt v₁ v₂ = .ok value) :
    evalExpr? cfg solm evm (.binary .lt lhs rhs) = .ok value := by
  simp [evalExpr?, hleft, hright, hop, EvalResult.bind, bind]

theorem attesterEvalIndex {cfg : Config} {solm : Frame} {evm : EVM.State}
    {base idx : Expr} {container key value : Value}
    (hbase : evalExpr? cfg solm evm base = .ok container)
    (hidx : evalExpr? cfg solm evm idx = .ok key)
    (hindex : evalIndex? container key = .ok value) :
    evalExpr? cfg solm evm (.index base idx) = .ok value := by
  simp [evalExpr?, hbase, hidx, hindex, EvalResult.bind, bind]

theorem attesterEvalRevocationData {cfg : Config} {solm : Frame} {evm : EVM.State}
    {uidExpr : Expr} {uid : Value}
    (huid : evalExpr? cfg solm evm uidExpr = .ok uid) :
    evalExpr? cfg solm evm (revocationData uidExpr) =
      .ok (attesterRevocationDataValue uid) := by
  simp [revocationData, attesterRevocationDataValue, evalExpr?, huid, evalExprList?,
    EvalResult.bind, bind, pure]

theorem attesterEvalMultiRevokeRequest {cfg : Config} {solm : Frame} {evm : EVM.State}
    {schemaExpr dataExpr : Expr} {schema : Value} {data : List Value}
    (hschema : evalExpr? cfg solm evm schemaExpr = .ok schema)
    (hdata : evalExpr? cfg solm evm dataExpr = .ok (.array data)) :
    evalExpr? cfg solm evm (.tupleLit [schemaExpr, dataExpr]) =
      .ok (.tuple [schema, .array data]) := by
  simp [evalExpr?, evalExprList?, hschema, hdata, EvalResult.bind, bind, pure]

theorem attesterEvalNewRevocationDataArray {cfg : Config} {solm : Frame}
    {evm : EVM.State} {lenExpr : Expr} {n : Nat}
    (hlen : evalExpr? cfg solm evm lenExpr = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg solm evm (.newArray revocationRequestDataSt lenExpr) =
      .ok (.array (List.replicate n attesterRevocationDataDefault)) := by
  simp [evalExpr?, hlen, revocationRequestDataSt, attesterRevocationDataDefault,
    attesterRevocationDataValue, bytes32St, bytes32Width, uint256St,
    defaultValue?, defaultValues?, EvalResult.bind, bind, pure]

theorem attesterEvalNewMultiRevokeRequestArray {cfg : Config} {solm : Frame}
    {evm : EVM.State} {lenExpr : Expr} {n : Nat}
    (hlen : evalExpr? cfg solm evm lenExpr = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg solm evm (.newArray multiRevocationRequestSt lenExpr) =
      .ok (.array (List.replicate n attesterMultiRevokeRequestDefault)) := by
  simp [evalExpr?, hlen, multiRevocationRequestSt, attesterMultiRevokeRequestDefault,
    revocationRequestDataSt, bytes32St, bytes32Width, uint256St, defaultValue?,
    defaultValues?, EvalResult.bind, bind, pure]

theorem attesterEvalUInt256NeZeroTrue {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {n : Nat}
    (hval : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hne : n ≠ 0) :
    evalExpr? cfg solm evm (.binary .ne expr (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, hval, evalBinaryOp?, hne, EvalResult.bind, bind, pure]

theorem attesterEvalUInt256NeZeroFalse {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {n : Nat}
    (hval : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hzero : n = 0) :
    evalExpr? cfg solm evm (.binary .ne expr (.intLit 0)) = .ok (.bool false) := by
  subst n
  simp [evalExpr?, hval, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem attesterEvalLocalArrayLength {cfg : Config} {solm : Frame} {evm : EVM.State}
    {name : Ident} {xs : List Value}
    (hget : solm.locals.get? name = some (.array xs)) :
    evalExpr? cfg solm evm (lenLocal name) = .ok (.int (Int.ofNat xs.length)) := by
  have hgetElem : solm.locals[name]? = some (.array xs) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [lenLocal, localRef, evalExpr?, readLocalPath?, hgetElem, EvalResult.bind, bind, pure]

theorem attesterAssignLocalVar {cfg : Config} {solm : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value}
    (hget : solm.locals.get? name = some old) :
    assignStorageRef? cfg solm evm .localVar (localRef name) value =
      .ok ({ solm with locals := solm.locals.insert name value }, evm) := by
  have hgetElem : solm.locals[name]? = some old := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [assignStorageRef?, localRef, hgetElem, updateLocalPath?, EvalResult.bind, bind, pure]

theorem attesterExecAssignLocalVar {cfg : Config} {solm : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value} {expr : Expr}
    (hrhs : evalExpr? cfg solm evm expr = .ok value)
    (hget : solm.locals.get? name = some old) :
    ExecStmt cfg solm evm (.assign .localVar (localRef name) expr)
      (.ok { solm with locals := solm.locals.insert name value } evm) :=
  ExecStmt.assign hrhs (attesterAssignLocalVar hget)

theorem attesterLookupNth?_exists {α : Type} :
    ∀ {xs : List α} {i : Nat}, i < xs.length → ∃ value, lookupNth? xs i = some value
  | [], _, h => by simp at h
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, h => by
      have hlt : i < xs.length := by
        simpa using Nat.succ_lt_succ_iff.mp h
      exact @attesterLookupNth?_exists α xs i hlt

theorem attesterUpdateNth?_exists {α : Type} :
    ∀ {xs : List α} {i : Nat}, i < xs.length → (value : α) →
      ∃ xs', updateNth? xs i value = some xs'
  | [], _, h, _ => by simp at h
  | _ :: xs, 0, _, value => by
      exact ⟨value :: xs, rfl⟩
  | x :: xs, i + 1, h, value => by
      have hlt : i < xs.length := by
        simpa using Nat.succ_lt_succ_iff.mp h
      obtain ⟨xs', hupdate⟩ := @attesterUpdateNth?_exists α xs i hlt value
      exact ⟨x :: xs', by simp [updateNth?, hupdate, bind, pure]⟩

theorem attesterAssignLocalArrayIndexOfUpdate {cfg : Config} {solm : Frame}
    {evm : EVM.State} {name : Ident} {idxExpr : Expr} {xs xs' : List Value}
    {i : Nat} {old value : Value}
    (hidx : evalExpr? cfg solm evm idxExpr = .ok (.int (Int.ofNat i)))
    (hget : solm.locals.get? name = some (.array xs))
    (hbounds : i < xs.length)
    (hlookup : lookupNth? xs i = some old)
    (hupdate : updateNth? xs i value = some xs') :
    assignStorageRef? cfg solm evm .localVar (localIndex name idxExpr) value =
      .ok ({ solm with locals := solm.locals.insert name (.array xs') }, evm) := by
  have hgetElem : solm.locals[name]? = some (.array xs) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  have hcheck : 0 ≤ (i : Int) ∧ (i : Int) < (xs.length : Int) := by
    constructor
    · exact Int.natCast_nonneg i
    · exact_mod_cast hbounds
  have hnotNeg : ¬ (i : Int) < 0 := not_lt_of_ge (Int.natCast_nonneg i)
  simp [assignStorageRef?, localIndex, hgetElem, updateLocalPath?, hidx, hcheck,
    lookupIndex?, updateIndex?, intToNat?, hnotNeg, hlookup, hupdate, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

theorem attesterExecAssignLocalArrayIndexOfUpdate {cfg : Config} {solm : Frame}
    {evm : EVM.State} {name : Ident} {idxExpr rhs : Expr} {xs xs' : List Value}
    {i : Nat} {old value : Value}
    (hrhs : evalExpr? cfg solm evm rhs = .ok value)
    (hidx : evalExpr? cfg solm evm idxExpr = .ok (.int (Int.ofNat i)))
    (hget : solm.locals.get? name = some (.array xs))
    (hbounds : i < xs.length)
    (hlookup : lookupNth? xs i = some old)
    (hupdate : updateNth? xs i value = some xs') :
    ExecStmt cfg solm evm (.assign .localVar (localIndex name idxExpr) rhs)
      (.ok { solm with locals := solm.locals.insert name (.array xs') } evm) :=
  ExecStmt.assign hrhs
    (attesterAssignLocalArrayIndexOfUpdate hidx hget hbounds hlookup hupdate)

def attesterMultiRevokeInnerSourceLoopCond : Expr :=
  .binary .lt (.var "j") (.var "uidLength")

def attesterMultiRevokeInnerSourceLoopBody : List Stmt :=
  [ arrSet "data" (.var "j") (revocationData (arrGet "uids" (.var "j"))),
    .assign .localVar (localRef "j") (add256 (.var "j") (.intLit 1)) ]

def attesterMultiRevokeInnerSourceLoopInv (uids : List Value)
    (v : Nat) (locals : Store) : Prop :=
  ∃ j,
    locals.get? "uids" = some (.array uids) ∧
    locals.get? "uidLength" = some (.int (Int.ofNat uids.length)) ∧
    locals.get? "data" = some (.array (attesterRevocationDataPrefix j uids)) ∧
    locals.get? "j" = some (.int (Int.ofNat j)) ∧
    j + v = uids.length ∧
    j ≤ uids.length

theorem attesterEvalVarOfGet {cfg : Config} {C : ContractDecl}
    {evm : EVM.State} {locals : Store} {name : Ident} {value : Value}
    (hget : locals.get? name = some value) :
    evalExpr? cfg { contract := C, locals := locals } evm (.var name) = .ok value := by
  have hgetElem : locals[name]? = some value := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  simp [evalExpr?, EvalResult.ofOption, hgetElem]

theorem attesterStoreGetInsertSelf {locals : Store} {name : Ident} {value : Value} :
    (locals.insert name value).get? name = some value := by
  rw [Std.HashMap.get?_eq_getElem?]
  simp

theorem attesterStoreGetInsertOfNe {locals : Store} {name other : Ident}
    {value old : Value}
    (hget : locals.get? name = some old)
    (hne : other ≠ name) :
    (locals.insert other value).get? name = some old := by
  have hgetElem : locals[name]? = some old := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  rw [Std.HashMap.get?_eq_getElem?]
  simp [Std.HashMap.getElem?_insert, hne, hgetElem]

theorem attesterEvalUInt256AddOne {cfg : Config} {C : ContractDecl}
    {evm : EVM.State} {locals : Store} {name : Ident} {i : Nat}
    (hget : locals.get? name = some (.int (Int.ofNat i)))
    (hbound : i + 1 < 2 ^ 256) :
    evalExpr? cfg { contract := C, locals := locals } evm
      (add256 (.var name) (.intLit 1)) =
      .ok (.int (Int.ofNat (i + 1))) := by
  have hgetElem : locals[name]? = some (.int (Int.ofNat i)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  have hnotNeg : ¬ (Int.ofNat i + 1 : Int) < 0 := by
    have hnonneg : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
    omega
  have hadd : (Int.ofNat i + 1 : Int) = Int.ofNat (i + 1) := by
    norm_num
  have hltInt : (Int.ofNat i + 1 : Int) < (2 : Int) ^ (256 : Nat) := by
    rw [hadd]
    simpa using (Int.ofNat_lt.mpr hbound)
  have hnotGe : ¬ (2 : Int) ^ (256 : Nat) ≤ (Int.ofNat i + 1 : Int) :=
    not_le_of_gt hltInt
  have hrange :
      0 ≤ (Int.ofNat i + 1 : Int) ∧
        (Int.ofNat i + 1 : Int) <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    constructor
    · exact le_of_not_gt hnotNeg
    · simpa using hltInt
  simp [add256, u256, uint256Int, evalExpr?, EvalResult.ofOption, hgetElem,
    evalBinaryOp?, EvalResult.bind, bind, pure]
  simpa using hrange

theorem attesterMultiRevokeInnerSourceLoopCondTrue
    (imm : AttesterImmutables) (evm : EVM.State) {locals : Store}
    {uids : List Value} {j : Nat}
    (hlen : locals.get? "uidLength" = some (.int (Int.ofNat uids.length)))
    (hj : locals.get? "j" = some (.int (Int.ofNat j)))
    (hlt : j < uids.length) :
    evalExpr? (config imm) { contract := contract imm, locals := locals } evm
      attesterMultiRevokeInnerSourceLoopCond = .ok (.bool true) := by
  exact attesterEvalBinaryLt
    (attesterEvalVarOfGet hj)
    (attesterEvalVarOfGet hlen)
    (by simp [evalBinaryOp?, hlt])

theorem attesterMultiRevokeInnerSourceLoopCondFalse
    (imm : AttesterImmutables) (evm : EVM.State) {locals : Store}
    {uids : List Value} {j : Nat}
    (hlen : locals.get? "uidLength" = some (.int (Int.ofNat uids.length)))
    (hj : locals.get? "j" = some (.int (Int.ofNat j)))
    (hnot : ¬ j < uids.length) :
    evalExpr? (config imm) { contract := contract imm, locals := locals } evm
      attesterMultiRevokeInnerSourceLoopCond = .ok (.bool false) := by
  exact attesterEvalBinaryLt
    (attesterEvalVarOfGet hj)
    (attesterEvalVarOfGet hlen)
    (by simp [evalBinaryOp?, hnot])

theorem attesterMultiRevokeInnerSourceLoop_step
    (imm : AttesterImmutables) (evm : EVM.State) {uids : List Value}
    (hlenBound : uids.length < 2 ^ 256)
    (hnorm : ∀ {j uid}, lookupNth? uids j = some uid →
      normalizeRawBoolWord? uid = .ok uid) :
    ∀ n locals, attesterMultiRevokeInnerSourceLoopInv uids (n + 1) locals →
      ∃ locals',
        ExecBlock (config imm) { contract := contract imm, locals := locals } evm
          attesterMultiRevokeInnerSourceLoopBody
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeInnerSourceLoopInv uids n locals' ∧
        ∃ j,
          locals' =
            (locals.insert "data" (.array (attesterRevocationDataPrefix (j + 1) uids))).insert
              "j" (.int (Int.ofNat (j + 1))) := by
  intro n locals hInv
  rcases hInv with ⟨j, huids, hlen, hdata, hj, hvar, hle⟩
  have hlt : j < uids.length := by omega
  obtain ⟨uid, huidLookup, hupdate⟩ :=
    attesterRevocationDataPrefix_update (uids := uids) (n := j) hlt
  have hdataLen :
      (attesterRevocationDataPrefix j uids).length = uids.length :=
    attesterRevocationDataPrefix_length j uids
  obtain ⟨old, hdataLookup⟩ :=
    attesterLookupNth?_exists
      (xs := attesterRevocationDataPrefix j uids) (i := j)
      (by rw [hdataLen]; exact hlt)
  let dataNext := attesterRevocationDataPrefix (j + 1) uids
  have hidxEval :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (.var "j") = .ok (.int (Int.ofNat j)) :=
    attesterEvalVarOfGet hj
  have huidsEval :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (.var "uids") = .ok (.array uids) :=
    attesterEvalVarOfGet huids
  have hindex :
      evalIndex? (.array uids) (.int (Int.ofNat j)) = .ok uid := by
    simp [evalIndex?, hlt, huidLookup, hnorm huidLookup]
  have hgetUid :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (arrGet "uids" (.var "j")) = .ok uid :=
    attesterEvalIndex huidsEval hidxEval hindex
  have hrhs :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (revocationData (arrGet "uids" (.var "j"))) =
        .ok (attesterRevocationDataValue uid) :=
    attesterEvalRevocationData hgetUid
  let L1 := locals.insert "data" (.array dataNext)
  have hstmtData :
      ExecStmt (config imm) { contract := contract imm, locals := locals } evm
        (arrSet "data" (.var "j") (revocationData (arrGet "uids" (.var "j"))))
        (.ok { contract := contract imm, locals := L1 } evm) := by
    simpa [arrSet, localIndex, dataNext, L1] using
      attesterExecAssignLocalArrayIndexOfUpdate
        (cfg := config imm) (solm := { contract := contract imm, locals := locals })
        (evm := evm) (name := "data") (idxExpr := .var "j")
        (rhs := revocationData (arrGet "uids" (.var "j")))
        (xs := attesterRevocationDataPrefix j uids) (xs' := dataNext)
        (i := j) (old := old) (value := attesterRevocationDataValue uid)
        hrhs hidxEval hdata (by rw [hdataLen]; exact hlt) hdataLookup
        (by simpa [dataNext] using hupdate)
  have hjL1 :
      L1.get? "j" = some (.int (Int.ofNat j)) := by
    have hjElem : locals["j"]? = some (.int (Int.ofNat j)) := by
      simpa [Std.HashMap.get?_eq_getElem?] using hj
    rw [Std.HashMap.get?_eq_getElem?]
    simp [L1, Std.HashMap.getElem?_insert, hjElem]
  have hincEval :
      evalExpr? (config imm) { contract := contract imm, locals := L1 } evm
        (add256 (.var "j") (.intLit 1)) =
        .ok (.int (Int.ofNat (j + 1))) := by
    exact attesterEvalUInt256AddOne
      (cfg := config imm) (C := contract imm) (evm := evm)
      (locals := L1) (name := "j") (i := j) hjL1 (by omega)
  let L2 := L1.insert "j" (.int (Int.ofNat (j + 1)))
  have hstmtInc :
      ExecStmt (config imm) { contract := contract imm, locals := L1 } evm
        (.assign .localVar (localRef "j") (add256 (.var "j") (.intLit 1)))
        (.ok { contract := contract imm, locals := L2 } evm) := by
    simpa [localRef, L2] using
      attesterExecAssignLocalVar
        (cfg := config imm) (solm := { contract := contract imm, locals := L1 })
        (evm := evm) (name := "j") (old := .int (Int.ofNat j))
        (value := .int (Int.ofNat (j + 1)))
        (expr := add256 (.var "j") (.intLit 1)) hincEval hjL1
  refine ⟨L2, ?_, ?_, j, rfl⟩
  · exact ExecBlock.consNormal hstmtData
      (ExecBlock.consNormal hstmtInc ExecBlock.nil)
  · refine ⟨j + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have huidsElem : locals["uids"]? = some (.array uids) := by
        simpa [Std.HashMap.get?_eq_getElem?] using huids
      rw [Std.HashMap.get?_eq_getElem?]
      simp [L2, L1, Std.HashMap.getElem?_insert, huidsElem]
    · have hlenElem : locals["uidLength"]? =
          some (.int (Int.ofNat uids.length)) := by
        simpa [Std.HashMap.get?_eq_getElem?] using hlen
      rw [Std.HashMap.get?_eq_getElem?]
      simp [L2, L1, Std.HashMap.getElem?_insert, hlenElem]
    · rw [Std.HashMap.get?_eq_getElem?]
      simp [L2, L1, Std.HashMap.getElem_insert, dataNext]
    · rw [Std.HashMap.get?_eq_getElem?]
      simp [L2]
    · omega
    · omega

theorem attesterMultiRevokeInnerSourceLoop_from_inv
    (imm : AttesterImmutables) (evm : EVM.State) {uids : List Value}
    (hlenBound : uids.length < 2 ^ 256)
    (hnorm : ∀ {j uid}, lookupNth? uids j = some uid →
      normalizeRawBoolWord? uid = .ok uid) :
    ∀ n locals, attesterMultiRevokeInnerSourceLoopInv uids n locals →
      ∃ locals',
        ExecStmt (config imm) { contract := contract imm, locals := locals } evm
          (.while attesterMultiRevokeInnerSourceLoopCond
            attesterMultiRevokeInnerSourceLoopBody)
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeInnerSourceLoopInv uids 0 locals' := by
  refine execWhile_var
    (cfg := config imm) (C := contract imm) (evm := evm)
    (cond := attesterMultiRevokeInnerSourceLoopCond)
    (body := attesterMultiRevokeInnerSourceLoopBody)
    (P := attesterMultiRevokeInnerSourceLoopInv uids) ?_ ?_ ?_
  · intro locals hInv
    rcases hInv with ⟨j, _huids, hlen, _hdata, hj, hvar, _hle⟩
    exact attesterMultiRevokeInnerSourceLoopCondFalse imm evm hlen hj (by omega)
  · intro n locals hInv
    rcases hInv with ⟨j, _huids, hlen, _hdata, hj, hvar, _hle⟩
    exact attesterMultiRevokeInnerSourceLoopCondTrue imm evm hlen hj (by omega)
  · intro n locals hInv
    obtain ⟨locals', hbody, hInv', _⟩ :=
      attesterMultiRevokeInnerSourceLoop_step imm evm hlenBound hnorm
        n locals hInv
    exact ⟨locals', hbody, hInv'⟩

theorem attesterMultiRevokeInnerSourceLoop_from_inv_keep
    (imm : AttesterImmutables) (evm : EVM.State) {uids : List Value}
    {Keep : Store → Prop}
    (hlenBound : uids.length < 2 ^ 256)
    (hnorm : ∀ {j uid}, lookupNth? uids j = some uid →
      normalizeRawBoolWord? uid = .ok uid)
    (hkeepData : ∀ {locals data}, Keep locals →
      Keep (locals.insert "data" (.array data)))
    (hkeepJ : ∀ {locals j}, Keep locals →
      Keep (locals.insert "j" (.int (Int.ofNat j)))) :
    ∀ n locals, attesterMultiRevokeInnerSourceLoopInv uids n locals → Keep locals →
      ∃ locals',
        ExecStmt (config imm) { contract := contract imm, locals := locals } evm
          (.while attesterMultiRevokeInnerSourceLoopCond
            attesterMultiRevokeInnerSourceLoopBody)
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeInnerSourceLoopInv uids 0 locals' ∧
        Keep locals' := by
  intro n locals hBase hKeep
  refine execWhile_var
    (cfg := config imm) (C := contract imm) (evm := evm)
    (cond := attesterMultiRevokeInnerSourceLoopCond)
    (body := attesterMultiRevokeInnerSourceLoopBody)
    (P := fun n locals =>
      attesterMultiRevokeInnerSourceLoopInv uids n locals ∧ Keep locals) ?_ ?_ ?_
    n locals ⟨hBase, hKeep⟩
  · intro locals hInv
    rcases hInv.1 with ⟨j, _huids, hlen, _hdata, hj, hvar, _hle⟩
    exact attesterMultiRevokeInnerSourceLoopCondFalse imm evm hlen hj (by omega)
  · intro n locals hInv
    rcases hInv.1 with ⟨j, _huids, hlen, _hdata, hj, hvar, _hle⟩
    exact attesterMultiRevokeInnerSourceLoopCondTrue imm evm hlen hj (by omega)
  · intro n locals hInv
    obtain ⟨locals', hbody, hInv', j, hlocals'⟩ :=
      attesterMultiRevokeInnerSourceLoop_step imm evm hlenBound hnorm
        n locals hInv.1
    refine ⟨locals', hbody, ?_⟩
    constructor
    · exact hInv'
    · rw [hlocals']
      exact hkeepJ (j := j + 1)
        (hkeepData (data := attesterRevocationDataPrefix (j + 1) uids) hInv.2)

theorem attesterMultiRevokeInnerSourceLoop
    (imm : AttesterImmutables) (evm : EVM.State) {uids : List Value}
    {locals : Store}
    (hlenBound : uids.length < 2 ^ 256)
    (hnorm : ∀ {j uid}, lookupNth? uids j = some uid →
      normalizeRawBoolWord? uid = .ok uid)
    (huids : locals.get? "uids" = some (.array uids))
    (hlen : locals.get? "uidLength" = some (.int (Int.ofNat uids.length)))
    (hdata : locals.get? "data" =
      some (.array (List.replicate uids.length attesterRevocationDataDefault)))
    (hj : locals.get? "j" = some (.int 0)) :
    ∃ locals',
      ExecStmt (config imm) { contract := contract imm, locals := locals } evm
        (.while attesterMultiRevokeInnerSourceLoopCond
          attesterMultiRevokeInnerSourceLoopBody)
        (.ok { contract := contract imm, locals := locals' } evm) ∧
      locals'.get? "data" = some (.array (attesterRevocationDataValues uids)) ∧
      locals'.get? "j" = some (.int (Int.ofNat uids.length)) := by
  have hdata0 :
      locals.get? "data" =
        some (.array (attesterRevocationDataPrefix 0 uids)) := by
    simpa [attesterRevocationDataPrefix_zero] using hdata
  have hinv : attesterMultiRevokeInnerSourceLoopInv uids uids.length locals := by
    refine ⟨0, huids, hlen, hdata0, ?_, by simp, by simp⟩
    simpa using hj
  obtain ⟨locals', hloop, hInvDone⟩ :=
    attesterMultiRevokeInnerSourceLoop_from_inv imm evm hlenBound hnorm
      uids.length locals hinv
  rcases hInvDone with ⟨j, _huids, _hlen, hdataDone, hjDone, hvar, _hle⟩
  have hjLen : j = uids.length := by omega
  refine ⟨locals', hloop, ?_, ?_⟩
  · simpa [hjLen, attesterRevocationDataPrefix_all] using hdataDone
  · simpa [hjLen] using hjDone

def attesterMultiRevokeOuterSourceLoopCond : Expr :=
  .binary .lt (.var "i") (.var "schemaLength")

def attesterMultiRevokeOuterSourceLoopBody : List Stmt :=
  [ .letDecl "uids" (some bytes32Array) (arrGet "schemaUids" (.var "i")),
    .letDecl "uidLength" (some uint256) (lenLocal "uids"),
    .require (.binary .ne (.var "uidLength") (.intLit 0)),
    .letDecl "data" (some (.dynamicArray revocationRequestDataTy))
      (.newArray revocationRequestDataSt (.var "uidLength")),
    .letDecl "j" (some uint256) (.intLit 0),
    .while attesterMultiRevokeInnerSourceLoopCond
      attesterMultiRevokeInnerSourceLoopBody,
    arrSet "multiRequests" (.var "i")
      (.tupleLit [arrGet "schemas" (.var "i"), .var "data"]),
    .assign .localVar (localRef "i") (add256 (.var "i") (.intLit 1)) ]

def attesterMultiRevokeOuterSourceLoopInv
    (schemas schemaUids : List Value) (v : Nat) (locals : Store) : Prop :=
  ∃ i,
    locals.get? "schemas" = some (.array schemas) ∧
    locals.get? "schemaUids" = some (.array schemaUids) ∧
    locals.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) ∧
    locals.get? "multiRequests" =
      some (.array (attesterMultiRevokeRequestValuesPrefix i schemas schemaUids)) ∧
    locals.get? "i" = some (.int (Int.ofNat i)) ∧
    i + v = schemas.length ∧
    i ≤ schemas.length

theorem attesterMultiRevokeOuterSourceLoopCondTrue
    (imm : AttesterImmutables) (evm : EVM.State) {locals : Store}
    {schemas : List Value} {i : Nat}
    (hlen : locals.get? "schemaLength" = some (.int (Int.ofNat schemas.length)))
    (hi : locals.get? "i" = some (.int (Int.ofNat i)))
    (hlt : i < schemas.length) :
    evalExpr? (config imm) { contract := contract imm, locals := locals } evm
      attesterMultiRevokeOuterSourceLoopCond = .ok (.bool true) := by
  exact attesterEvalBinaryLt
    (attesterEvalVarOfGet hi)
    (attesterEvalVarOfGet hlen)
    (by simp [evalBinaryOp?, hlt])

theorem attesterMultiRevokeOuterSourceLoopCondFalse
    (imm : AttesterImmutables) (evm : EVM.State) {locals : Store}
    {schemas : List Value} {i : Nat}
    (hlen : locals.get? "schemaLength" = some (.int (Int.ofNat schemas.length)))
    (hi : locals.get? "i" = some (.int (Int.ofNat i)))
    (hnot : ¬ i < schemas.length) :
    evalExpr? (config imm) { contract := contract imm, locals := locals } evm
      attesterMultiRevokeOuterSourceLoopCond = .ok (.bool false) := by
  exact attesterEvalBinaryLt
    (attesterEvalVarOfGet hi)
    (attesterEvalVarOfGet hlen)
    (by simp [evalBinaryOp?, hnot])

theorem attesterMultiRevokeOuterSourceLoopBody_revert_emptyCurrent
    (imm : AttesterImmutables) (evm : EVM.State) {locals : Store}
    {schemaUids : List Value} {i : Nat}
    (hschemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hi : locals.get? "i" = some (.int (Int.ofNat i)))
    (hlt : i < schemaUids.length)
    (hlookup : lookupNth? schemaUids i = some (.array [])) :
    ExecBlock (config imm) { contract := contract imm, locals := locals } evm
      attesterMultiRevokeOuterSourceLoopBody .reverted := by
  have hschemaUidsEval :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (.var "schemaUids") = .ok (.array schemaUids) :=
    attesterEvalVarOfGet hschemaUids
  have hiEval :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (.var "i") = .ok (.int (Int.ofNat i)) :=
    attesterEvalVarOfGet hi
  have hindexUids :
      evalIndex? (.array schemaUids) (.int (Int.ofNat i)) = .ok (.array []) := by
    simp [evalIndex?, normalizeRawBoolWord?, hlt, hlookup]
  have huidsExpr :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (arrGet "schemaUids" (.var "i")) = .ok (.array []) :=
    attesterEvalIndex hschemaUidsEval hiEval hindexUids
  let L1 := locals.insert "uids" (.array [])
  have hstmtUids :
      ExecStmt (config imm) { contract := contract imm, locals := locals } evm
        (.letDecl "uids" (some bytes32Array) (arrGet "schemaUids" (.var "i")))
        (.ok { contract := contract imm, locals := L1 } evm) := by
    simpa [L1] using ExecStmt.letDecl huidsExpr
  have huidsL1 : L1.get? "uids" = some (.array []) := by
    simp [L1]
  have hlenExpr :
      evalExpr? (config imm) { contract := contract imm, locals := L1 } evm
        (lenLocal "uids") = .ok (.int 0) := by
    simpa using attesterEvalLocalArrayLength
      (cfg := config imm) (solm := { contract := contract imm, locals := L1 })
      (evm := evm) (name := "uids") (xs := []) huidsL1
  let L2 := L1.insert "uidLength" (.int 0)
  have hstmtUidLength :
      ExecStmt (config imm) { contract := contract imm, locals := L1 } evm
        (.letDecl "uidLength" (some uint256) (lenLocal "uids"))
        (.ok { contract := contract imm, locals := L2 } evm) := by
    simpa [L2] using ExecStmt.letDecl hlenExpr
  have hlenL2 : L2.get? "uidLength" = some (.int 0) := by
    simp [L2]
  have hrequireEval :
      evalExpr? (config imm) { contract := contract imm, locals := L2 } evm
        (.binary .ne (.var "uidLength") (.intLit 0)) = .ok (.bool false) :=
    attesterEvalUInt256NeZeroFalse (attesterEvalVarOfGet hlenL2) rfl
  unfold attesterMultiRevokeOuterSourceLoopBody
  exact ExecBlock.consNormal hstmtUids
    (ExecBlock.consNormal hstmtUidLength
      (ExecBlock.consRevert (ExecStmt.requireFalse hrequireEval)))

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeOuterSourceLoop_step_current
    (imm : AttesterImmutables) (evm : EVM.State)
    {schemas schemaUids : List Value}
    (hschemasBound : schemas.length < 2 ^ 256)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema) :
    ∀ n locals, attesterMultiRevokeOuterSourceLoopInv schemas schemaUids (n + 1) locals →
      (∀ {idx value}, lookupNth? schemaUids idx = some value →
        idx + (n + 1) = schemas.length →
        ∃ uids,
          value = .array uids ∧
          uids.length ≠ 0 ∧
          uids.length < 2 ^ 256 ∧
          (∀ {j uid}, lookupNth? uids j = some uid →
            normalizeRawBoolWord? uid = .ok uid)) →
      ∃ locals',
        ExecBlock (config imm) { contract := contract imm, locals := locals } evm
          attesterMultiRevokeOuterSourceLoopBody
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeOuterSourceLoopInv schemas schemaUids n locals' := by
  intro n locals hInv huidssOkCurrent
  rcases hInv with
    ⟨i, hschemas, hschemaUids, hschemaLength, hrequests, hi, hvar, hle⟩
  have hlt : i < schemas.length := by omega
  obtain ⟨schema, hschemaLookup⟩ :=
    attesterLookupNth?_exists (xs := schemas) (i := i) hlt
  have hltSchemaUids : i < schemaUids.length := by omega
  obtain ⟨schemaUidValue, hschemaUidLookupValue⟩ :=
    attesterLookupNth?_exists (xs := schemaUids) (i := i) hltSchemaUids
  obtain ⟨uids, hschemaUidValue, huidsNe, huidsBound, huidsNorm⟩ :=
    huidssOkCurrent hschemaUidLookupValue hvar
  have hschemaUidLookup : lookupNth? schemaUids i = some (.array uids) := by
    simpa [hschemaUidValue] using hschemaUidLookupValue
  have hschemaUidsEval :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (.var "schemaUids") = .ok (.array schemaUids) :=
    attesterEvalVarOfGet hschemaUids
  have hiEval :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (.var "i") = .ok (.int (Int.ofNat i)) :=
    attesterEvalVarOfGet hi
  have hindexUids :
      evalIndex? (.array schemaUids) (.int (Int.ofNat i)) = .ok (.array uids) := by
    simp [evalIndex?, normalizeRawBoolWord?, hltSchemaUids, hschemaUidLookup]
  have huidsExpr :
      evalExpr? (config imm) { contract := contract imm, locals := locals } evm
        (arrGet "schemaUids" (.var "i")) = .ok (.array uids) :=
    attesterEvalIndex hschemaUidsEval hiEval hindexUids
  let L1 := locals.insert "uids" (.array uids)
  have hstmtUids :
      ExecStmt (config imm) { contract := contract imm, locals := locals } evm
        (.letDecl "uids" (some bytes32Array) (arrGet "schemaUids" (.var "i")))
        (.ok { contract := contract imm, locals := L1 } evm) := by
    simpa [L1] using ExecStmt.letDecl huidsExpr
  have huidsL1 : L1.get? "uids" = some (.array uids) := by
    simp [L1]
  have hlenExpr :
      evalExpr? (config imm) { contract := contract imm, locals := L1 } evm
        (lenLocal "uids") = .ok (.int (Int.ofNat uids.length)) :=
    attesterEvalLocalArrayLength huidsL1
  let L2 := L1.insert "uidLength" (.int (Int.ofNat uids.length))
  have hstmtUidLength :
      ExecStmt (config imm) { contract := contract imm, locals := L1 } evm
        (.letDecl "uidLength" (some uint256) (lenLocal "uids"))
        (.ok { contract := contract imm, locals := L2 } evm) := by
    simpa [L2] using ExecStmt.letDecl hlenExpr
  have hlenL2 : L2.get? "uidLength" = some (.int (Int.ofNat uids.length)) := by
    simp [L2]
  have hrequireEval :
      evalExpr? (config imm) { contract := contract imm, locals := L2 } evm
        (.binary .ne (.var "uidLength") (.intLit 0)) = .ok (.bool true) :=
    attesterEvalUInt256NeZeroTrue (attesterEvalVarOfGet hlenL2) huidsNe
  have hstmtRequire :
      ExecStmt (config imm) { contract := contract imm, locals := L2 } evm
        (.require (.binary .ne (.var "uidLength") (.intLit 0)))
        (.ok { contract := contract imm, locals := L2 } evm) :=
    ExecStmt.requireTrue hrequireEval
  have hnewData :
      evalExpr? (config imm) { contract := contract imm, locals := L2 } evm
        (.newArray revocationRequestDataSt (.var "uidLength")) =
        .ok (.array (List.replicate uids.length attesterRevocationDataDefault)) :=
    attesterEvalNewRevocationDataArray (attesterEvalVarOfGet hlenL2)
  let L3 := L2.insert "data"
    (.array (List.replicate uids.length attesterRevocationDataDefault))
  have hstmtDataDecl :
      ExecStmt (config imm) { contract := contract imm, locals := L2 } evm
        (.letDecl "data" (some (.dynamicArray revocationRequestDataTy))
          (.newArray revocationRequestDataSt (.var "uidLength")))
        (.ok { contract := contract imm, locals := L3 } evm) := by
    simpa [L3] using ExecStmt.letDecl hnewData
  have hjExpr :
      evalExpr? (config imm) { contract := contract imm, locals := L3 } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  let L4 := L3.insert "j" (.int 0)
  have hstmtJDecl :
      ExecStmt (config imm) { contract := contract imm, locals := L3 } evm
        (.letDecl "j" (some uint256) (.intLit 0))
        (.ok { contract := contract imm, locals := L4 } evm) := by
    simpa [L4] using ExecStmt.letDecl hjExpr
  have huidsL4 : L4.get? "uids" = some (.array uids) := by
    have huidsL2 : L2.get? "uids" = some (.array uids) := by
      simpa [L2] using
        (attesterStoreGetInsertOfNe (locals := L1) (name := "uids")
          (other := "uidLength") (value := .int (Int.ofNat uids.length))
          huidsL1 (by decide))
    have huidsL3 : L3.get? "uids" = some (.array uids) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "uids")
          (other := "data")
          (value := .array (List.replicate uids.length attesterRevocationDataDefault))
          huidsL2 (by decide))
    simpa [L4] using
      (attesterStoreGetInsertOfNe (locals := L3) (name := "uids")
        (other := "j") (value := .int 0) huidsL3 (by decide))
  have hlenL4 :
      L4.get? "uidLength" = some (.int (Int.ofNat uids.length)) := by
    have hlenL3 :
        L3.get? "uidLength" = some (.int (Int.ofNat uids.length)) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "uidLength")
          (other := "data")
          (value := .array (List.replicate uids.length attesterRevocationDataDefault))
          hlenL2 (by decide))
    simpa [L4] using
      (attesterStoreGetInsertOfNe (locals := L3) (name := "uidLength")
        (other := "j") (value := .int 0) hlenL3 (by decide))
  have hdataL4 :
      L4.get? "data" =
        some (.array (List.replicate uids.length attesterRevocationDataDefault)) := by
    have hdataL3 :
        L3.get? "data" =
          some (.array (List.replicate uids.length attesterRevocationDataDefault)) := by
      simp [L3]
    simpa [L4] using
      (attesterStoreGetInsertOfNe (locals := L3) (name := "data")
        (other := "j") (value := .int 0) hdataL3 (by decide))
  have hjL4 : L4.get? "j" = some (.int 0) := by
    simp [L4]
  have hinnerInv :
      attesterMultiRevokeInnerSourceLoopInv uids uids.length L4 := by
    refine ⟨0, huidsL4, hlenL4, ?_, ?_, by simp, by simp⟩
    · simpa [attesterRevocationDataPrefix_zero] using hdataL4
    · simpa using hjL4
  let requestsPrefix := attesterMultiRevokeRequestValuesPrefix i schemas schemaUids
  let Keep : Store → Prop := fun L =>
    L.get? "schemas" = some (.array schemas) ∧
    L.get? "schemaUids" = some (.array schemaUids) ∧
    L.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) ∧
    L.get? "multiRequests" = some (.array requestsPrefix) ∧
    L.get? "i" = some (.int (Int.ofNat i))
  have hKeepL4 : Keep L4 := by
    dsimp [Keep, requestsPrefix]
    have hschemasL1 : L1.get? "schemas" = some (.array schemas) := by
      simpa [L1] using
        (attesterStoreGetInsertOfNe (locals := locals) (name := "schemas")
          (other := "uids") (value := .array uids) hschemas (by decide))
    have hschemasL2 : L2.get? "schemas" = some (.array schemas) := by
      simpa [L2] using
        (attesterStoreGetInsertOfNe (locals := L1) (name := "schemas")
          (other := "uidLength") (value := .int (Int.ofNat uids.length))
          hschemasL1 (by decide))
    have hschemasL3 : L3.get? "schemas" = some (.array schemas) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "schemas")
          (other := "data")
          (value := .array (List.replicate uids.length attesterRevocationDataDefault))
          hschemasL2 (by decide))
    have hschemasL4 : L4.get? "schemas" = some (.array schemas) := by
      simpa [L4] using
        (attesterStoreGetInsertOfNe (locals := L3) (name := "schemas")
          (other := "j") (value := .int 0) hschemasL3 (by decide))
    have hschemaUidsL1 : L1.get? "schemaUids" = some (.array schemaUids) := by
      simpa [L1] using
        (attesterStoreGetInsertOfNe (locals := locals) (name := "schemaUids")
          (other := "uids") (value := .array uids) hschemaUids (by decide))
    have hschemaUidsL2 : L2.get? "schemaUids" = some (.array schemaUids) := by
      simpa [L2] using
        (attesterStoreGetInsertOfNe (locals := L1) (name := "schemaUids")
          (other := "uidLength") (value := .int (Int.ofNat uids.length))
          hschemaUidsL1 (by decide))
    have hschemaUidsL3 : L3.get? "schemaUids" = some (.array schemaUids) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "schemaUids")
          (other := "data")
          (value := .array (List.replicate uids.length attesterRevocationDataDefault))
          hschemaUidsL2 (by decide))
    have hschemaUidsL4 : L4.get? "schemaUids" = some (.array schemaUids) := by
      simpa [L4] using
        (attesterStoreGetInsertOfNe (locals := L3) (name := "schemaUids")
          (other := "j") (value := .int 0) hschemaUidsL3 (by decide))
    have hschemaLengthL1 :
        L1.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
      simpa [L1] using
        (attesterStoreGetInsertOfNe (locals := locals) (name := "schemaLength")
          (other := "uids") (value := .array uids) hschemaLength (by decide))
    have hschemaLengthL2 :
        L2.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
      simpa [L2] using
        (attesterStoreGetInsertOfNe (locals := L1) (name := "schemaLength")
          (other := "uidLength") (value := .int (Int.ofNat uids.length))
          hschemaLengthL1 (by decide))
    have hschemaLengthL3 :
        L3.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "schemaLength")
          (other := "data")
          (value := .array (List.replicate uids.length attesterRevocationDataDefault))
          hschemaLengthL2 (by decide))
    have hschemaLengthL4 :
        L4.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
      simpa [L4] using
        (attesterStoreGetInsertOfNe (locals := L3) (name := "schemaLength")
          (other := "j") (value := .int 0) hschemaLengthL3 (by decide))
    have hrequestsL1 : L1.get? "multiRequests" = some (.array requestsPrefix) := by
      simpa [L1, requestsPrefix] using
        (attesterStoreGetInsertOfNe (locals := locals) (name := "multiRequests")
          (other := "uids") (value := .array uids) hrequests (by decide))
    have hrequestsL2 : L2.get? "multiRequests" = some (.array requestsPrefix) := by
      simpa [L2] using
        (attesterStoreGetInsertOfNe (locals := L1) (name := "multiRequests")
          (other := "uidLength") (value := .int (Int.ofNat uids.length))
          hrequestsL1 (by decide))
    have hrequestsL3 : L3.get? "multiRequests" = some (.array requestsPrefix) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "multiRequests")
          (other := "data")
          (value := .array (List.replicate uids.length attesterRevocationDataDefault))
          hrequestsL2 (by decide))
    have hrequestsL4 : L4.get? "multiRequests" = some (.array requestsPrefix) := by
      simpa [L4] using
        (attesterStoreGetInsertOfNe (locals := L3) (name := "multiRequests")
          (other := "j") (value := .int 0) hrequestsL3 (by decide))
    have hiL1 : L1.get? "i" = some (.int (Int.ofNat i)) := by
      simpa [L1] using
        (attesterStoreGetInsertOfNe (locals := locals) (name := "i")
          (other := "uids") (value := .array uids) hi (by decide))
    have hiL2 : L2.get? "i" = some (.int (Int.ofNat i)) := by
      simpa [L2] using
        (attesterStoreGetInsertOfNe (locals := L1) (name := "i")
          (other := "uidLength") (value := .int (Int.ofNat uids.length))
          hiL1 (by decide))
    have hiL3 : L3.get? "i" = some (.int (Int.ofNat i)) := by
      simpa [L3] using
        (attesterStoreGetInsertOfNe (locals := L2) (name := "i")
          (other := "data")
          (value := .array (List.replicate uids.length attesterRevocationDataDefault))
          hiL2 (by decide))
    have hiL4 : L4.get? "i" = some (.int (Int.ofNat i)) := by
      simpa [L4] using
        (attesterStoreGetInsertOfNe (locals := L3) (name := "i")
          (other := "j") (value := .int 0) hiL3 (by decide))
    constructor
    · exact hschemasL4
    constructor
    · exact hschemaUidsL4
    constructor
    · exact hschemaLengthL4
    constructor
    · exact hrequestsL4
    · exact hiL4
  have hkeepData : ∀ {L data}, Keep L → Keep (L.insert "data" (.array data)) := by
    intro L data hK
    rcases hK with ⟨hs, hsu, hsl, hmr, hiK⟩
    exact ⟨attesterStoreGetInsertOfNe hs (by decide),
      attesterStoreGetInsertOfNe hsu (by decide),
      attesterStoreGetInsertOfNe hsl (by decide),
      attesterStoreGetInsertOfNe hmr (by decide),
      attesterStoreGetInsertOfNe hiK (by decide)⟩
  have hkeepJ : ∀ {L j}, Keep L → Keep (L.insert "j" (.int (Int.ofNat j))) := by
    intro L j hK
    rcases hK with ⟨hs, hsu, hsl, hmr, hiK⟩
    exact ⟨attesterStoreGetInsertOfNe hs (by decide),
      attesterStoreGetInsertOfNe hsu (by decide),
      attesterStoreGetInsertOfNe hsl (by decide),
      attesterStoreGetInsertOfNe hmr (by decide),
      attesterStoreGetInsertOfNe hiK (by decide)⟩
  obtain ⟨L5, hinnerLoop, hinnerDone, hKeepDone⟩ :=
    attesterMultiRevokeInnerSourceLoop_from_inv_keep
      (imm := imm) (evm := evm) (uids := uids) (Keep := Keep)
      huidsBound huidsNorm hkeepData hkeepJ uids.length L4 hinnerInv hKeepL4
  rcases hinnerDone with
    ⟨jDone, _huidsDone, _hlenDone, hdataDone, _hjDone, hinnerVar, _hinnerLe⟩
  have hjDoneEq : jDone = uids.length := by omega
  have hdataFinal :
      L5.get? "data" = some (.array (attesterRevocationDataValues uids)) := by
    simpa [hjDoneEq, attesterRevocationDataPrefix_all] using hdataDone
  rcases hKeepDone with ⟨hschemas5, hschemaUids5, hschemaLength5, hrequests5, hi5⟩
  have hschemasEval5 :
      evalExpr? (config imm) { contract := contract imm, locals := L5 } evm
        (.var "schemas") = .ok (.array schemas) :=
    attesterEvalVarOfGet hschemas5
  have hiEval5 :
      evalExpr? (config imm) { contract := contract imm, locals := L5 } evm
        (.var "i") = .ok (.int (Int.ofNat i)) :=
    attesterEvalVarOfGet hi5
  have hindexSchema :
      evalIndex? (.array schemas) (.int (Int.ofNat i)) = .ok schema := by
    simp [evalIndex?, hlt, hschemaLookup, hschemaNorm hschemaLookup]
  have hschemaExpr :
      evalExpr? (config imm) { contract := contract imm, locals := L5 } evm
        (arrGet "schemas" (.var "i")) = .ok schema :=
    attesterEvalIndex hschemasEval5 hiEval5 hindexSchema
  have hdataExpr :
      evalExpr? (config imm) { contract := contract imm, locals := L5 } evm
        (.var "data") = .ok (.array (attesterRevocationDataValues uids)) :=
    attesterEvalVarOfGet hdataFinal
  have hrequestExpr :
      evalExpr? (config imm) { contract := contract imm, locals := L5 } evm
        (.tupleLit [arrGet "schemas" (.var "i"), .var "data"]) =
        .ok (attesterMultiRevokeRequestValue schema uids) := by
    simpa [attesterMultiRevokeRequestValue] using
      attesterEvalMultiRevokeRequest hschemaExpr hdataExpr
  have hrequestsLen :
      requestsPrefix.length = schemas.length := by
    simp [requestsPrefix, attesterMultiRevokeRequestValuesPrefix_length]
  obtain ⟨oldRequest, hrequestLookup⟩ :=
    attesterLookupNth?_exists (xs := requestsPrefix) (i := i)
      (by rw [hrequestsLen]; exact hlt)
  have hrequestUpdate :
      updateNth? requestsPrefix i (attesterMultiRevokeRequestValue schema uids) =
        some (attesterMultiRevokeRequestValuesPrefix (i + 1) schemas schemaUids) := by
    simpa [requestsPrefix] using
      attesterMultiRevokeRequestValuesPrefix_update
        (schemas := schemas) (schemaUids := schemaUids) (n := i)
        (schema := schema) (uids := uids) hschemaLookup hschemaUidLookup
  let requestsNext := attesterMultiRevokeRequestValuesPrefix (i + 1) schemas schemaUids
  let L6 := L5.insert "multiRequests" (.array requestsNext)
  have hstmtSetRequest :
      ExecStmt (config imm) { contract := contract imm, locals := L5 } evm
        (arrSet "multiRequests" (.var "i")
          (.tupleLit [arrGet "schemas" (.var "i"), .var "data"]))
        (.ok { contract := contract imm, locals := L6 } evm) := by
    simpa [arrSet, localIndex, requestsPrefix, requestsNext, L6] using
      attesterExecAssignLocalArrayIndexOfUpdate
        (cfg := config imm) (solm := { contract := contract imm, locals := L5 })
        (evm := evm) (name := "multiRequests") (idxExpr := .var "i")
        (rhs := .tupleLit [arrGet "schemas" (.var "i"), .var "data"])
        (xs := requestsPrefix) (xs' := requestsNext)
        (i := i) (old := oldRequest)
        (value := attesterMultiRevokeRequestValue schema uids)
        hrequestExpr hiEval5 hrequests5 (by rw [hrequestsLen]; exact hlt)
        hrequestLookup (by simpa [requestsPrefix, requestsNext] using hrequestUpdate)
  have hiL6 : L6.get? "i" = some (.int (Int.ofNat i)) := by
    simpa [L6] using
      (attesterStoreGetInsertOfNe (locals := L5) (name := "i")
        (other := "multiRequests") (value := .array requestsNext) hi5 (by decide))
  have hincEval :
      evalExpr? (config imm) { contract := contract imm, locals := L6 } evm
        (add256 (.var "i") (.intLit 1)) =
        .ok (.int (Int.ofNat (i + 1))) := by
    exact attesterEvalUInt256AddOne
      (cfg := config imm) (C := contract imm) (evm := evm)
      (locals := L6) (name := "i") (i := i) hiL6 (by omega)
  let L7 := L6.insert "i" (.int (Int.ofNat (i + 1)))
  have hstmtInc :
      ExecStmt (config imm) { contract := contract imm, locals := L6 } evm
        (.assign .localVar (localRef "i") (add256 (.var "i") (.intLit 1)))
        (.ok { contract := contract imm, locals := L7 } evm) := by
    simpa [localRef, L7] using
      attesterExecAssignLocalVar
        (cfg := config imm) (solm := { contract := contract imm, locals := L6 })
        (evm := evm) (name := "i") (old := .int (Int.ofNat i))
        (value := .int (Int.ofNat (i + 1)))
        (expr := add256 (.var "i") (.intLit 1)) hincEval hiL6
  refine ⟨L7, ?_, ?_⟩
  · exact ExecBlock.consNormal hstmtUids
      (ExecBlock.consNormal hstmtUidLength
        (ExecBlock.consNormal hstmtRequire
          (ExecBlock.consNormal hstmtDataDecl
            (ExecBlock.consNormal hstmtJDecl
              (ExecBlock.consNormal hinnerLoop
                (ExecBlock.consNormal hstmtSetRequest
                  (ExecBlock.consNormal hstmtInc ExecBlock.nil)))))))
  · refine ⟨i + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hs6 : L6.get? "schemas" = some (.array schemas) := by
        simpa [L6] using
          (attesterStoreGetInsertOfNe (locals := L5) (name := "schemas")
            (other := "multiRequests") (value := .array requestsNext) hschemas5
            (by decide))
      simpa [L7] using
        (attesterStoreGetInsertOfNe (locals := L6) (name := "schemas")
          (other := "i") (value := .int (Int.ofNat (i + 1))) hs6 (by decide))
    · have hsu6 : L6.get? "schemaUids" = some (.array schemaUids) := by
        simpa [L6] using
          (attesterStoreGetInsertOfNe (locals := L5) (name := "schemaUids")
            (other := "multiRequests") (value := .array requestsNext) hschemaUids5
            (by decide))
      simpa [L7] using
        (attesterStoreGetInsertOfNe (locals := L6) (name := "schemaUids")
          (other := "i") (value := .int (Int.ofNat (i + 1))) hsu6 (by decide))
    · have hsl6 :
          L6.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
        simpa [L6] using
          (attesterStoreGetInsertOfNe (locals := L5) (name := "schemaLength")
            (other := "multiRequests") (value := .array requestsNext) hschemaLength5
            (by decide))
      simpa [L7] using
        (attesterStoreGetInsertOfNe (locals := L6) (name := "schemaLength")
          (other := "i") (value := .int (Int.ofNat (i + 1))) hsl6 (by decide))
    · have hmr6 :
          L6.get? "multiRequests" = some (.array requestsNext) := by
        simp [L6]
      simpa [requestsNext, L7] using
        (attesterStoreGetInsertOfNe (locals := L6) (name := "multiRequests")
          (other := "i") (value := .int (Int.ofNat (i + 1))) hmr6
          (by decide))
    · simp [L7]
    · omega
    · omega

theorem attesterMultiRevokeOuterSourceLoop_step
    (imm : AttesterImmutables) (evm : EVM.State)
    {schemas schemaUids : List Value}
    (hschemasBound : schemas.length < 2 ^ 256)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (huidssOk : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length ≠ 0 ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid)) :
    ∀ n locals, attesterMultiRevokeOuterSourceLoopInv schemas schemaUids (n + 1) locals →
      ∃ locals',
        ExecBlock (config imm) { contract := contract imm, locals := locals } evm
          attesterMultiRevokeOuterSourceLoopBody
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeOuterSourceLoopInv schemas schemaUids n locals' := by
  intro n locals hInv
  exact attesterMultiRevokeOuterSourceLoop_step_current
    (imm := imm) (evm := evm) (schemas := schemas) (schemaUids := schemaUids)
    hschemasBound hlenEq hschemaNorm n locals hInv
    (by
      intro idx value hlookup _hcurrent
      exact huidssOk hlookup)

theorem attesterMultiRevokeOuterSourceLoop_step_or_revert
    (imm : AttesterImmutables) (evm : EVM.State)
    {schemas schemaUids : List Value}
    (hschemasBound : schemas.length < 2 ^ 256)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (huidssShape : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid)) :
    ∀ n locals, attesterMultiRevokeOuterSourceLoopInv schemas schemaUids (n + 1) locals →
      (ExecBlock (config imm) { contract := contract imm, locals := locals } evm
          attesterMultiRevokeOuterSourceLoopBody .reverted) ∨
      ∃ locals',
        ExecBlock (config imm) { contract := contract imm, locals := locals } evm
          attesterMultiRevokeOuterSourceLoopBody
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeOuterSourceLoopInv schemas schemaUids n locals' := by
  intro n locals hInv
  have hInvOrig := hInv
  rcases hInv with
    ⟨i, _hschemas, hschemaUids, _hschemaLength, _hrequests, hi, hvar, _hle⟩
  have hlt : i < schemas.length := by omega
  have hltSchemaUids : i < schemaUids.length := by omega
  obtain ⟨schemaUidValue, hschemaUidLookupValue⟩ :=
    attesterLookupNth?_exists (xs := schemaUids) (i := i) hltSchemaUids
  obtain ⟨uids, hschemaUidValue, huidsBound, huidsNorm⟩ :=
    huidssShape hschemaUidLookupValue
  cases uids with
  | nil =>
      have hlookupEmpty : lookupNth? schemaUids i = some (.array []) := by
        simpa [hschemaUidValue] using hschemaUidLookupValue
      exact .inl
        (attesterMultiRevokeOuterSourceLoopBody_revert_emptyCurrent
          (imm := imm) (evm := evm) (locals := locals)
          (schemaUids := schemaUids) (i := i) hschemaUids hi hltSchemaUids hlookupEmpty)
  | cons uid rest =>
      have huidsNe : (uid :: rest).length ≠ 0 := by simp
      refine .inr ?_
      exact attesterMultiRevokeOuterSourceLoop_step_current
        (imm := imm) (evm := evm) (schemas := schemas) (schemaUids := schemaUids)
        hschemasBound hlenEq hschemaNorm n locals hInvOrig
        (by
          intro idx value hlookup hidxVar
          have hidxEq : idx = i := by omega
          subst idx
          have hvalueEq : value = .array (uid :: rest) := by
            have hs : some value = some (.array (uid :: rest)) := by
              rw [← hlookup]
              simpa [hschemaUidValue] using hschemaUidLookupValue
            cases hs
            rfl
          exact ⟨uid :: rest, hvalueEq, huidsNe, huidsBound, huidsNorm⟩)

theorem attesterMultiRevokeOuterSourceLoop_from_inv_or_revert
    (imm : AttesterImmutables) (evm : EVM.State)
    {schemas schemaUids : List Value}
    (hschemasBound : schemas.length < 2 ^ 256)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (huidssShape : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid)) :
    ∀ n locals, attesterMultiRevokeOuterSourceLoopInv schemas schemaUids n locals →
      (∃ locals',
        ExecStmt (config imm) { contract := contract imm, locals := locals } evm
          (.while attesterMultiRevokeOuterSourceLoopCond
            attesterMultiRevokeOuterSourceLoopBody)
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeOuterSourceLoopInv schemas schemaUids 0 locals') ∨
      ExecStmt (config imm) { contract := contract imm, locals := locals } evm
        (.while attesterMultiRevokeOuterSourceLoopCond
          attesterMultiRevokeOuterSourceLoopBody)
        .reverted := by
  intro n
  induction n with
  | zero =>
      intro locals hInv
      rcases hInv with ⟨i, _hschemas, _hschemaUids, hlen, _hrequests, hi, hvar, _hle⟩
      exact .inl ⟨locals,
        ExecStmt.whileFalse
          (attesterMultiRevokeOuterSourceLoopCondFalse imm evm hlen hi (by omega)),
        ⟨i, _hschemas, _hschemaUids, hlen, _hrequests, hi, hvar, _hle⟩⟩
  | succ n ih =>
      intro locals hInv
      have hInvOrig := hInv
      rcases hInv with ⟨i, _hschemas, _hschemaUids, hlen, _hrequests, hi, hvar, _hle⟩
      have hcond :=
        attesterMultiRevokeOuterSourceLoopCondTrue imm evm hlen hi (by omega)
      rcases
        attesterMultiRevokeOuterSourceLoop_step_or_revert
          (imm := imm) (evm := evm) (schemas := schemas) (schemaUids := schemaUids)
          hschemasBound hlenEq hschemaNorm huidssShape n locals hInvOrig
        with hbodyRevert | hbodyOk
      · exact .inr (ExecStmt.whileRevert hcond hbodyRevert)
      · rcases hbodyOk with ⟨locals', hbody, hInv'⟩
        rcases ih locals' hInv' with hdone | hrev
        · rcases hdone with ⟨locals'', hloop, hInvDone⟩
          exact .inl ⟨locals'', ExecStmt.whileTrue hcond hbody hloop, hInvDone⟩
        · exact .inr (ExecStmt.whileTrue hcond hbody hrev)

theorem attesterMultiRevokeOuterSourceLoop_from_inv
    (imm : AttesterImmutables) (evm : EVM.State)
    {schemas schemaUids : List Value}
    (hschemasBound : schemas.length < 2 ^ 256)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (huidssOk : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length ≠ 0 ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid)) :
    ∀ n locals, attesterMultiRevokeOuterSourceLoopInv schemas schemaUids n locals →
      ∃ locals',
        ExecStmt (config imm) { contract := contract imm, locals := locals } evm
          (.while attesterMultiRevokeOuterSourceLoopCond
            attesterMultiRevokeOuterSourceLoopBody)
          (.ok { contract := contract imm, locals := locals' } evm) ∧
        attesterMultiRevokeOuterSourceLoopInv schemas schemaUids 0 locals' := by
  refine execWhile_var
    (cfg := config imm) (C := contract imm) (evm := evm)
    (cond := attesterMultiRevokeOuterSourceLoopCond)
    (body := attesterMultiRevokeOuterSourceLoopBody)
    (P := attesterMultiRevokeOuterSourceLoopInv schemas schemaUids) ?_ ?_ ?_
  · intro locals hInv
    rcases hInv with ⟨i, _hschemas, _hschemaUids, hlen, _hrequests, hi, hvar, _hle⟩
    exact attesterMultiRevokeOuterSourceLoopCondFalse imm evm hlen hi (by omega)
  · intro n locals hInv
    rcases hInv with ⟨i, _hschemas, _hschemaUids, hlen, _hrequests, hi, hvar, _hle⟩
    exact attesterMultiRevokeOuterSourceLoopCondTrue imm evm hlen hi (by omega)
  · intro n locals hInv
    obtain ⟨locals', hbody, hInv'⟩ :=
      attesterMultiRevokeOuterSourceLoop_step
        (imm := imm) (evm := evm) (schemas := schemas) (schemaUids := schemaUids)
        hschemasBound hlenEq hschemaNorm huidssOk n locals hInv
    exact ⟨locals', hbody, hInv'⟩

theorem attesterMultiRevokeOuterSourceLoop
    (imm : AttesterImmutables) (evm : EVM.State)
    {schemas schemaUids : List Value} {locals : Store}
    (hschemasBound : schemas.length < 2 ^ 256)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (huidssOk : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length ≠ 0 ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid))
    (hschemas : locals.get? "schemas" = some (.array schemas))
    (hschemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hschemaLength : locals.get? "schemaLength" =
      some (.int (Int.ofNat schemas.length)))
    (hrequests : locals.get? "multiRequests" =
      some (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)))
    (hi : locals.get? "i" = some (.int 0)) :
    ∃ locals',
      ExecStmt (config imm) { contract := contract imm, locals := locals } evm
        (.while attesterMultiRevokeOuterSourceLoopCond
          attesterMultiRevokeOuterSourceLoopBody)
        (.ok { contract := contract imm, locals := locals' } evm) ∧
      locals'.get? "multiRequests" =
        some (.array
          (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) ∧
      locals'.get? "i" = some (.int (Int.ofNat schemas.length)) := by
  have hrequests0 :
      locals.get? "multiRequests" =
        some (.array (attesterMultiRevokeRequestValuesPrefix 0 schemas schemaUids)) := by
    simpa [attesterMultiRevokeRequestValuesPrefix_zero] using hrequests
  have hInv :
      attesterMultiRevokeOuterSourceLoopInv schemas schemaUids schemas.length locals := by
    refine ⟨0, hschemas, hschemaUids, hschemaLength, hrequests0, ?_, by simp, by simp⟩
    simpa using hi
  obtain ⟨locals', hloop, hInvDone⟩ :=
    attesterMultiRevokeOuterSourceLoop_from_inv
      (imm := imm) (evm := evm) (schemas := schemas) (schemaUids := schemaUids)
      hschemasBound hlenEq hschemaNorm huidssOk schemas.length locals hInv
  rcases hInvDone with
    ⟨i, _hschemasDone, _hschemaUidsDone, _hschemaLengthDone, hrequestsDone,
      hiDone, hvar, _hle⟩
  have hiLen : i = schemas.length := by omega
  refine ⟨locals', hloop, ?_, ?_⟩
  · simpa [hiLen] using hrequestsDone
  · simpa [hiLen] using hiDone

end Benchmarks.EAS.Attester
