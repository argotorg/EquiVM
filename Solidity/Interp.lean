import Solidity.Semantics

/-!
# Executable interpreter

A fuel-indexed definitional interpreter over the same AST and helpers as the relational rules
(`Semantics/Exec.lean`), in the monad `IM = ExceptT ByteArray Option`: `throw d` is a revert with
data `d`, `failure` is "stuck or out of fuel".  Every member of the mutual block is structurally
recursive on the fuel (each recursive call uses the predecessor), and the case analysis mirrors
the rules one-to-one, which is what the equivalence theorem (`Theory/InterpEquiv.lean`) exploits.
-/

namespace Solidity

abbrev IM := ExceptT ByteArray Option

instance : Alternative IM where
  failure := ExceptT.mk none
  orElse a b := ExceptT.mk (match a.run with | none => (b ()).run | some r => some r)

namespace Interp

def liftOp {α} : Op α → IM α
  | none => failure
  | some (.error p) => throw p.data
  | some (.ok a) => pure a

def liftOpt {α} : Option α → IM α
  | none => failure
  | some a => pure a

def guard' (b : Bool) : IM Unit := if b then pure () else failure

/-! ## EVM bridges (deterministic mirrors of `Calls.lean`) -/

def callViaEVM (o : Oracle) (m : Machine) (target : EVM.Address) (value : Nat) (calldata : EVM.Bytes)
    (perm : Bool) (gas : Ethereum.UInt256) : Bool × Machine × EVM.Bytes :=
  let valueWord := EVM.Word.ofNat value
  let bal := (m.evm.accountMap.find? m.this |>.getD default).balance
  if valueWord ≤ bal ∧ m.evm.executionEnv.depth ≠ 1024 then
    let (cA', σ', _, A', z, out) :=
      Ethereum.EVM.Θ m.evm.executionEnv.blobVersionedHashes m.evm.createdAccounts
        m.evm.genesisBlockHeader m.evm.blocks m.evm.accountMap m.evm.σ₀ (subInput o m)
        m.this m.evm.executionEnv.sender target (Ethereum.toExecute m.evm.accountMap target)
        gas (.ofNat m.evm.executionEnv.gasPrice) valueWord valueWord calldata
        (m.evm.executionEnv.depth + 1) m.evm.executionEnv.header perm
    (z, afterCall m cA' σ' A', out)
  else
    (false, { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 }, ByteArray.empty)

def delegateCallViaEVM (o : Oracle) (m : Machine) (target : EVM.Address) (calldata : EVM.Bytes)
    (gas : Ethereum.UInt256) : Bool × Machine × EVM.Bytes :=
  if m.evm.executionEnv.depth ≠ 1024 then
    let (cA', σ', _, A', z, out) :=
      Ethereum.EVM.Θ m.evm.executionEnv.blobVersionedHashes m.evm.createdAccounts
        m.evm.genesisBlockHeader m.evm.blocks m.evm.accountMap m.evm.σ₀ (subInput o m)
        m.evm.executionEnv.source m.evm.executionEnv.sender m.this
        (Ethereum.toExecute m.evm.accountMap target) gas
        (.ofNat m.evm.executionEnv.gasPrice) ⟨0⟩ m.evm.executionEnv.weiValue calldata
        (m.evm.executionEnv.depth + 1) m.evm.executionEnv.header m.evm.executionEnv.perm
    (z, afterCall m cA' σ' A', out)
  else
    (false, { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 }, ByteArray.empty)

/-- Creation (`new C(...)`) via `Λ`: `(address, machine, success, returndata)`; `none` without
    creation code for `name`. -/
def newViaEVM (cfg : Config) (o : Oracle) (m : Machine) (name : Ident) (value : Nat) (args : List ABI.ABIValue)
    (salt : Option ByteArray) : Option (EVM.Address × Machine × Bool × EVM.Bytes) :=
  match cfg.creationCode name args with
  | none => none
  | some initCode =>
    let valueWord := EVM.Word.ofNat value
    let creator := m.evm.accountMap.find? m.this |>.getD default
    if valueWord ≤ creator.balance ∧ m.evm.executionEnv.depth ≠ 1024 ∧ creator.nonce.toNat < 2 ^ 64 - 1 ∧
        initCode.size ≤ 49152 then
      let σStar := m.evm.accountMap.insert m.this { creator with nonce := creator.nonce + ⟨1⟩ }
      let (addr, cA', σ', _, A', z, out) :=
        Ethereum.EVM.Lambda m.evm.executionEnv.blobVersionedHashes m.evm.createdAccounts
          m.evm.genesisBlockHeader m.evm.blocks σStar m.evm.σ₀ (subInput o m) m.this
          m.evm.executionEnv.sender (o.callGas m.tick) (.ofNat m.evm.executionEnv.gasPrice) valueWord initCode
          (m.evm.executionEnv.depth + 1) salt m.evm.executionEnv.header m.evm.executionEnv.perm
      some (addr, afterCall m cA' σ' A', z, out)
    else
      some (EVM.address 0, { m with tick := m.tick + 1 }, false, ByteArray.empty)

/-! ## The interpreter -/

variable (cfg : Config) (o : Oracle) (fc : FlatContract)

abbrev EV := IM (Value × Frame × Machine)

def isAbiFn (f : Ident) : Bool :=
  f == "encode" || f == "encodePacked" || f == "encodeWithSelector" || f == "encodeWithSignature" || f == "decode"

mutual

def evalExpr : Nat → Frame → Machine → Expr → EV
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | .lit l => do let v ← liftOpt (literalValue l); pure (v, fr, m)
    | .this => pure (.contract fc.name m.this, fr, m)
    | .ident x =>
      match fr.get? x with
      | some l => pure (l.val, fr, m)
      | none =>
        match fc.var? x with
        | some v =>
          match v.mutability with
          | .constant => do
            let some e := v.init | failure
            evalExpr fuel fr m e
          | .immutable => do let val ← liftOpt (immutableValue cfg fc.types fr v); pure (val, fr, m)
          | .mutable => do let val ← liftOpt (loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty); pure (val, fr, m)
        | none => failure
    | .member e f =>
      if directMember fc fr e then
        match e with
        | .ident obj =>
          if isEnvObj obj then
            if obj == "msg" && f == "data" then
              let (v, m') := allocBytes m false m.evm.executionEnv.calldata
              pure (v, fr, m')
            else do let v ← liftOpt (envMember m obj f); pure (v, fr, m)
          else do
            let some en := fc.types.enum? none obj | failure
            let i ← liftOpt (indexOf en.members f)
            pure (.enum obj i, fr, m)
        | .call (.ident "type") [] (.positional [.typeExpr ty]) => do
          let v ← liftOpt (typeMember fc ty f); pure (v, fr, m)
        | _ => failure
      else evalMember fuel fr m e f
    | .index e i => do
      let (base, fr1, m1) ← evalExpr fuel fr m e
      let (iv, fr2, m2) ← evalExpr fuel fr1 m1 i
      match base with
      | .storageRef er ty =>
        let (er', ty') ← liftOp (storageIndex cfg fc.types m2.evm m2.heap er ty iv)
        let v ← liftOpt (loadIfScalar cfg fc.types m2.evm er' ty')
        pure (v, fr2, m2)
      | .memRef obj =>
        let v ← liftOp (memIndex m2.heap obj iv)
        if isRaw v then
          match v with
          | .raw ty w =>
            match validateRaw ty w with
            | .ok v' => pure (v', fr2, m2)
            | .error d => throw d
          | _ => failure
        else pure (v, fr2, m2)
      | _ => failure
    | .call callee opts args => evalCall fuel fr m callee opts args
    | .unary op e =>
      if isIncDec op then do
        let (lv, fr1, m1) ← evalLValue fuel fr m e
        let cur ← liftOp (readLValue cfg fc.types fr1 m1 lv)
        let nv ← liftOp (binop (!fr1.unchecked) (incDecOp op) cur (.literal 1))
        let (fr2, m2) ← liftOp (assign cfg fc.types fr1 m1 lv nv)
        pure (if isPrefix op then nv else cur, fr2, m2)
      else if op == .delete then do
        let (lv, fr1, m1) ← evalLValue fuel fr m e
        match lv with
        | .local x =>
          let some l := fr1.get? x | failure
          let some (z, h') := zeroObj fc.types fuelDefault l.ty 0 m1.heap | failure
          pure (.unit, fr1.setVal x z, { m1 with heap := h' })
        | .storage er ty =>
          let evm' ← liftOp (clearStorage cfg fc.types fuelDefault m1.evm er ty)
          pure (.unit, fr1, { m1 with evm := evm' })
        | _ => failure
      else do
        let (v, fr1, m1) ← evalExpr fuel fr m e
        let r ← liftOp (unop (!fr1.unchecked) op v)
        pure (r, fr1, m1)
    | .binary op a b =>
      if op == .and then do
        let (va, fr1, m1) ← evalExpr fuel fr m a
        match va with
        | .bool false => pure (.bool false, fr1, m1)
        | .bool true =>
          let (vb, fr2, m2) ← evalExpr fuel fr1 m1 b
          match vb with
          | .bool y => pure (.bool y, fr2, m2)
          | _ => failure
        | _ => failure
      else if op == .or then do
        let (va, fr1, m1) ← evalExpr fuel fr m a
        match va with
        | .bool true => pure (.bool true, fr1, m1)
        | .bool false =>
          let (vb, fr2, m2) ← evalExpr fuel fr1 m1 b
          match vb with
          | .bool y => pure (.bool y, fr2, m2)
          | _ => failure
        | _ => failure
      else do
        let (vb, fr1, m1) ← evalExpr fuel fr m b
        let (va, fr2, m2) ← evalExpr fuel fr1 m1 a
        let v ← liftOp (binop (!fr2.unchecked) op va vb)
        pure (v, fr2, m2)
    | .cond c t e => do
      let (cv, fr1, m1) ← evalExpr fuel fr m c
      match cv with
      | .bool true => evalExpr fuel fr1 m1 t
      | .bool false => evalExpr fuel fr1 m1 e
      | _ => failure
    | .assign op lhs rhs => do
      let (v, fr1, m1) ← evalExpr fuel fr m rhs
      if isTupleExpr lhs then
        match op, lhs, v with
        | .assign, .tuple lhss, .tuple vs =>
          let (fr2, m2) ← assignTuple fuel fr1 m1 lhss vs
          pure (.tuple vs, fr2, m2)
        | _, _, _ => failure
      else
        let (lv, fr2, m2) ← evalLValue fuel fr1 m1 lhs
        if op == .assign then
          let (fr3, m3) ← liftOp (assign cfg fc.types fr2 m2 lv v)
          pure (v, fr3, m3)
        else
          let cur ← liftOp (readLValue cfg fc.types fr2 m2 lv)
          let r ← liftOp (binop (!fr2.unchecked) (assignOp op) cur v)
          let (fr3, m3) ← liftOp (assign cfg fc.types fr2 m2 lv r)
          pure (r, fr3, m3)
    | .tuple es => do
      let es' ← liftOpt (es.mapM fun x => x)
      let (vs, fr1, m1) ← evalExprs fuel fr m es'
      pure (.tuple vs, fr1, m1)
    | .arrayLit es => do
      let (vs, fr1, m1) ← evalExprs fuel fr m es
      let (v, m2) ← liftOp (arrayLitObj fc.types m1 vs)
      pure (v, fr1, m2)
    | _ => failure

/-- `e.f` with an evaluated receiver. -/
def evalMember : Nat → Frame → Machine → Expr → Ident → EV
  | 0, _, _, _, _ => failure
  | fuel+1, fr, m, e, f => do
    let (v, fr1, m1) ← evalExpr fuel fr m e
    match v with
    | .storageRef er ty =>
      if f == "length" then
        let n ← liftOp (storageLength cfg m1.evm er ty)
        pure (wordNat n, fr1, m1)
      else
        let (er', fty) ← liftOpt (storageField fc.types er ty f)
        let r ← liftOpt (loadIfScalar cfg fc.types m1.evm er' fty)
        pure (r, fr1, m1)
    | .memRef obj =>
      if f == "length" then do let n ← liftOpt (memLength m1.heap obj); pure (wordNat n, fr1, m1)
      else do let r ← liftOpt (memField m1.heap obj f); pure (r, fr1, m1)
    | .fixedBytes n _ => if f == "length" then pure (wordNat (n.val + 1), fr1, m1) else failure
    | v =>
      if f == "balance" then do
        let a ← liftOpt (addrNat v)
        pure (wordNat (balanceOf m1.evm (EVM.address a)), fr1, m1)
      else failure

def evalCall : Nat → Frame → Machine → Expr → List CallOpt → Args → EV
  | 0, _, _, _, _, _ => failure
  | fuel+1, fr, m, callee, opts, args =>
    match callee, opts, args with
    -- conversions
    | .typeExpr ty, [], .positional [a] => do
      let (v, fr1, m1) ← evalExpr fuel fr m a
      let (v', h') ← liftOp (explicitConv fc.types m1.heap v ty)
      pure (v', fr1, { m1 with heap := h' })
    -- contract creation / memory allocation
    | .new ty, _, _ =>
      match newContract? fc ty with
      | some (c, tys) => do
        let value ← evalValueOpt fuel fr m (valueOpt opts)
        let salt ← evalSaltOpt fuel value.2.1 value.2.2 (saltOpt opts)
        let es ← liftOpt (argExprsAny args)
        let (vs, fr3, m3) ← evalExprs fuel salt.2.1 salt.2.2 es
        let (svs, m4) ← liftOp (abiArgs cfg fc.types m3 tys vs)
        let (a, m5, z, out) ← liftOpt (newViaEVM cfg o m4 c value.1 svs salt.1)
        if !z then throw out
        pure (.contract c a, fr3, m5)
      | none =>
        match opts, args with
        | [], .positional [n] => do
          let (nv, fr1, m1) ← evalExpr fuel fr m n
          let len ← liftOpt (natValue nv)
          guard' (!(isValueType fc.types ty))
          let (v, h') ← liftOpt (zeroObj fc.types fuelDefault ty len m1.heap)
          pure (v, fr1, { m1 with heap := h' })
        | _, _ => failure
    -- builtins and internal calls
    | .ident f, [], _ =>
      if isBuiltinFn f then evalBuiltin fuel fr m f args else evalNamedCall fuel fr m f [] args
    -- member callees: `super.f`, `abi.f`, a library, or a call on an evaluated receiver
    | .member recv f, _, _ =>
      if isSuperExpr recv then
        if opts.isEmpty then do
          let es ← liftOpt (argExprsAny args)
          let (vs, fr1, m1) ← evalExprs fuel fr m es
          let fn ← liftOpt (resolveOverload fc.types m1.heap fc (superCands fc fr.here f) vs)
          let rets ← callFn fuel fr1 m1 fn vs
          pure (retValue rets.1, fr1, rets.2)
        else failure
      else if isEnvObj (headIdent recv) then
        match recv, opts, args with
        | .ident "abi", [], .positional es => if isAbiFn f then evalAbi fuel fr m f es else failure
        | _, _, _ => failure
      else if libraryRecv fc fr recv then
        match recv with
        | .ident l =>
          if opts.isEmpty then do
            let some lib := fc.library? l | failure
            let es ← liftOpt (argExprsAny args)
            let (vs, fr1, m1) ← evalExprs fuel fr m es
            let d ← liftOpt (resolveDecl fc.types m1.heap (lib.functions.filter (·.name == f)) vs)
            let rets ← callFn fuel fr1 m1 ⟨0, l, d⟩ vs
            pure (retValue rets.1, fr1, rets.2)
          else failure
        | _ => failure
      else if baseRecv fc fr recv then
        match recv with
        | .ident b =>
          if opts.isEmpty then do
            let es ← liftOpt (argExprsAny args)
            let (vs, fr1, m1) ← evalExprs fuel fr m es
            let fn ← liftOpt (resolveOverload fc.types m1.heap fc (baseCands fc b f) vs)
            let rets ← callFn fuel fr1 m1 fn vs
            pure (retValue rets.1, fr1, rets.2)
          else failure
        | _ => failure
      else evalMemberCall fuel fr m recv f opts args
    | _, _, _ => failure

/-- The builtin functions (`isBuiltinFn`). -/
def evalBuiltin : Nat → Frame → Machine → Ident → Args → EV
  | 0, _, _, _, _ => failure
  | fuel+1, fr, m, f, args =>
    match f, args with
    | "require", .positional (c :: rest) => do
      let (cv, fr1, m1) ← evalExpr fuel fr m c
      match cv, rest with
      | .bool true, _ => pure (.unit, fr1, m1)
      | .bool false, [] => throw ByteArray.empty
      | .bool false, [msg] =>
        if isCustomError fc msg then
          match msg with
          | .call (.ident err) [] eargs => do
            let ei ← liftOpt (fc.error? err)
            let es ← liftOpt (argExprs (paramNames ei.decl.params) eargs)
            let (vs, _, m2) ← evalExprs fuel fr1 m1 es
            let (svs, _) ← liftOp (abiArgs cfg fc.types m2 (ei.decl.params.map (·.ty)) vs)
            let d ← liftOpt (customErrorData ei.sigStr ei.sig.paramTypes svs)
            throw d
          | _ => failure
        else do
          let (mv, _, m2) ← evalExpr fuel fr1 m1 msg
          let s ← liftOpt (bytesArg m2.heap mv)
          throw (errorStringData s)
      | _, _ => failure
    | "assert", .positional [c] => do
      let (cv, fr1, m1) ← evalExpr fuel fr m c
      match cv with
      | .bool true => pure (.unit, fr1, m1)
      | .bool false => throw (panicData 0x01)
      | _ => failure
    | "revert", .positional [] => throw ByteArray.empty
    | "revert", .positional [msg] => do
      let (mv, _, m1) ← evalExpr fuel fr m msg
      let s ← liftOpt (bytesArg m1.heap mv)
      throw (errorStringData s)
    | "keccak256", .positional [b] => do
      let (v, fr1, m1) ← evalExpr fuel fr m b
      let s ← liftOpt (bytesArg m1.heap v)
      pure (.fixedBytes ⟨31, by decide⟩ (ffi.KEC s).toList, fr1, m1)
    | "gasleft", .positional [] =>
      pure (.uint ⟨256, by decide⟩ (o.gasleft m.tick).toNat, fr, { m with tick := m.tick + 1 })
    | "ecrecover", .positional [hsh, v, r, s] => do
      let (vs, fr1, m1) ← evalExprs fuel fr m [hsh, v, r, s]
      let (svs, m2) ← liftOp (abiArgs cfg fc.types m1 ecrecoverParamTys vs)
      let bs ← liftOpt (ABI.encodeABIValues? ecrecoverAbiTys svs)
      let (z, m3, out) := callViaEVM o m2 (EVM.address 1) 0 bs.toByteArray false (calleeGas o m2 none 0)
      if z then pure (ecrecoverResult out, fr1, m3) else throw out
    | f, .positional [x, y, k] =>
      if f == "addmod" || f == "mulmod" then do
        let (vs, fr1, m1) ← evalExprs fuel fr m [x, y, k]
        let [xv, yv, kv] := vs | failure
        let a ← liftOpt (natValue xv); let b ← liftOpt (natValue yv); let c ← liftOpt (natValue kv)
        if c = 0 then throw (panicData 0x12)
        pure (wordNat (if f == "addmod" then (a + b) % c else (a * b) % c), fr1, m1)
      else failure
    | _, _ => failure

/-- `f(args)` for a plain identifier callee: internal function, struct literal, or user-type conversion. -/
def evalNamedCall : Nat → Frame → Machine → Ident → List CallOpt → Args → EV
  | 0, _, _, _, _, _ => failure
  | fuel+1, fr, m, f, opts, args => do
    guard' (fr.get? f).isNone
    if fc.fnsNamed f ≠ [] then
      let es ← liftOpt (argExprsAny args)
      let (vs, fr1, m1) ← evalExprs fuel fr m es
      let fn ← liftOpt (resolveOverload fc.types m1.heap fc (fc.fnsNamed f) vs)
      let rets ← callFn fuel fr1 m1 fn vs
      pure (retValue rets.1, fr1, rets.2)
    else
      match fc.types.struct? none f with
      | some sd => do
        let es ← liftOpt (argExprs (sd.fields.map fun fl => some fl.2) args)
        let (vs, fr1, m1) ← evalExprs fuel fr m es
        let (v, m2) ← liftOp (structObj cfg fc.types m1 sd vs)
        pure (v, fr1, m2)
      | none =>
        if (fc.var? f).isNone && ((fc.types.contractKind? f).isSome || (fc.types.enum? none f).isSome) then
          match args with
          | .positional [a] => evalCall fuel fr m (.typeExpr (.user none f)) opts (.positional [a])
          | _ => failure
        else failure

def evalAbi : Nat → Frame → Machine → Ident → List Expr → EV
  | 0, _, _, _, _ => failure
  | fuel+1, fr, m, f, es => do
    match f with
    | "decode" =>
      match es with
      | [d, tyArg] =>
        let (dv, fr1, m1) ← evalExpr fuel fr m d
        let s ← liftOpt (bytesArg m1.heap dv)
        let tys ← liftOpt (typeArgs tyArg)
        let atys ← liftOpt (tys.mapM (abiTypeOf fc.types))
        match ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode atys s with
        | none => throw ByteArray.empty
        | some svs =>
          let (vs, h') ← liftOpt (ofAbiList fc.types tys svs m1.heap)
          pure (retValue vs, fr1, { m1 with heap := h' })
      | _ => failure
    | "encodeWithSelector" =>
      match es with
      | sel :: rest =>
        let (vs0, fr1, m1) ← evalExprs fuel fr m (sel :: rest)
        let (.fixedBytes n sb) :: vs := vs0 | failure
        guard' (n.val == 3)
        let tys ← liftOpt (vs.mapM (abiTyOfValue fc.types m1.heap))
        let (svs, m2) ← liftOp (abiArgsAbi cfg fc.types m1 tys vs)
        let bs ← liftOpt (ABI.encodeABIValues? tys svs)
        let (v, m3) := allocBytes m2 false ((ByteArray.mk sb.toArray) ++ bs.toByteArray)
        pure (v, fr1, m3)
      | _ => failure
    | "encodeWithSignature" =>
      match es with
      | sig :: rest =>
        let (vs0, fr1, m1) ← evalExprs fuel fr m (sig :: rest)
        let sv :: vs := vs0 | failure
        let s ← liftOpt (bytesArg m1.heap sv)
        let tys ← liftOpt (vs.mapM (abiTyOfValue fc.types m1.heap))
        let (svs, m2) ← liftOp (abiArgsAbi cfg fc.types m1 tys vs)
        let bs ← liftOpt (ABI.encodeABIValues? tys svs)
        let (v, m3) := allocBytes m2 false ((ffi.KEC s).extract 0 4 ++ bs.toByteArray)
        pure (v, fr1, m3)
      | _ => failure
    | "encode" =>
      let (vs, fr1, m1) ← evalExprs fuel fr m es
      let tys ← liftOpt (vs.mapM (abiTyOfValue fc.types m1.heap))
      let (svs, m2) ← liftOp (abiArgsAbi cfg fc.types m1 tys vs)
      let bs ← liftOpt (ABI.encodeABIValues? tys svs)
      let (v, m3) := allocBytes m2 false bs.toByteArray
      pure (v, fr1, m3)
    | "encodePacked" =>
      let (vs, fr1, m1) ← evalExprs fuel fr m es
      let tys ← liftOpt (vs.mapM (abiTyOfValue fc.types m1.heap))
      let (svs, m2) ← liftOp (abiArgsAbi cfg fc.types m1 tys vs)
      let parts ← liftOpt ((tys.zip svs).mapM fun (t, sv) => ABI.encodePackedValue? t sv)
      let (v, m3) := allocBytes m2 false parts.flatten.toByteArray
      pure (v, fr1, m3)
    | _ => failure

/-- `recv.f{opts}(args)` with an evaluated receiver. -/
def evalMemberCall : Nat → Frame → Machine → Expr → Ident → List CallOpt → Args → EV
  | 0, _, _, _, _, _, _ => failure
  | fuel+1, fr, m, recv, f, opts, args => do
    guard' (!(memberCallDirect fc fr recv))
    let (rv, fr1, m1) ← evalExpr fuel fr m recv
    if specialMemberCall rv f then
      match rv, f with
      | .storageRef er (.dynArray e), "push" =>
        guard' opts.isEmpty
        match args with
        | .positional [x] =>
          let (v, fr2, m2) ← evalExpr fuel fr1 m1 x
          let m3 ← liftOp (storagePush cfg fc.types m2 er e (some v))
          pure (.unit, fr2, m3)
        | .positional [] =>
          let m2 ← liftOp (storagePush cfg fc.types m1 er e none)
          pure (.unit, fr1, m2)
        | _ => failure
      | .storageRef er (.dynArray e), "pop" =>
        guard' opts.isEmpty
        match args with
        | .positional [] =>
          let m2 ← liftOp (storagePop cfg fc.types m1 er e)
          pure (.unit, fr1, m2)
        | _ => failure
      | .contract c a, _ =>
        let value ← evalValueOpt fuel fr1 m1 (valueOpt opts)
        let gasReq ← evalGasOpt fuel value.2.1 value.2.2 (gasOpt opts)
        let (fr3, m3) := (gasReq.2.1, gasReq.2.2)
        let es ← liftOpt (argExprsAny args)
        let (vs, fr4, m4) ← evalExprs fuel fr3 m3 es
        let d ← liftOpt (resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs)
        if d.returns.isEmpty && codeSize m4.evm a = 0 then throw ByteArray.empty
        let (sigStr, ptys, rtys) ← liftOpt (externalSig fc.types d)
        let (svs, m5) ← liftOp (abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs)
        let bs ← liftOpt (ABI.encodeABIValues? ptys svs)
        let perm := m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure
        let (z, m6, out) := callViaEVM o m5 a value.1 (selectorOf sigStr ++ bs.toByteArray) perm
          (calleeGas o m5 gasReq.1 value.1)
        if !z then throw out
        match decodeRets cfg fc.types m6 d.returns rtys out with
        | some (rets, m7) => pure (retValue rets, fr4, m7)
        | none => throw ByteArray.empty
      | rv, "call" | rv, "staticcall" =>
        match addrNat rv, args with
        | some a, .positional [dataE] =>
          let value ← evalValueOpt fuel fr1 m1 (valueOpt opts)
          let gasReq ← evalGasOpt fuel value.2.1 value.2.2 (gasOpt opts)
          let (dv, fr4, m4) ← evalExpr fuel gasReq.2.1 gasReq.2.2 dataE
          let data ← liftOpt (bytesArg m4.heap dv)
          let (z, m5, out) := callViaEVM o m4 (EVM.address a) value.1 data (f == "call" && m4.evm.executionEnv.perm)
            (calleeGas o m4 gasReq.1 value.1)
          let (ov, m6) := allocBytes m5 false out
          pure (.tuple [.bool z, ov], fr4, m6)
        | _, _ => failure
      | rv, "delegatecall" =>
        match addrNat rv, args with
        | some a, .positional [dataE] =>
          let gasReq ← evalGasOpt fuel fr1 m1 (gasOpt opts)
          let (dv, fr3, m3) ← evalExpr fuel gasReq.2.1 gasReq.2.2 dataE
          let data ← liftOpt (bytesArg m3.heap dv)
          let (z, m4, out) := delegateCallViaEVM o m3 (EVM.address a) data (calleeGas o m3 gasReq.1 0)
          let (ov, m5) := allocBytes m4 false out
          pure (.tuple [.bool z, ov], fr3, m5)
        | _, _ => failure
      | rv, "transfer" | rv, "send" =>
        guard' opts.isEmpty
        match addrNat rv, args with
        | some a, .positional [amt] =>
          let (av, fr2, m2) ← evalExpr fuel fr1 m1 amt
          let value ← liftOpt (natValue av)
          let (z, m3, out) := callViaEVM o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm
            (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value)
          if f == "transfer" then
            if z then pure (.unit, fr2, m3) else throw out
          else pure (.bool z, fr2, m3)
        | _, _ => failure
      | _, _ => failure
    else
      -- `using L for T`
      guard' opts.isEmpty
      match usingLibrary fc fr.here (receiverTy m1.heap rv) with
      | [lib] =>
        let es ← liftOpt (argExprsAny args)
        let (vs, fr2, m2) ← evalExprs fuel fr1 m1 es
        let d ← liftOpt (resolveDecl fc.types m2.heap (lib.functions.filter (·.name == f)) (rv :: vs))
        let rets ← callFn fuel fr2 m2 ⟨0, lib.name, d⟩ (rv :: vs)
        pure (retValue rets.1, fr2, rets.2)
      | _ => failure

def evalValueOpt : Nat → Frame → Machine → Option Expr → IM (Nat × Frame × Machine)
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | none => pure (0, fr, m)
    | some e => do
      let (v, fr1, m1) ← evalExpr fuel fr m e
      let n ← liftOpt (natValue v)
      pure (n, fr1, m1)

def evalGasOpt : Nat → Frame → Machine → Option Expr → IM (Option Nat × Frame × Machine)
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | none => pure (none, fr, m)
    | some e => do
      let (v, fr1, m1) ← evalExpr fuel fr m e
      let n ← liftOpt (natValue v)
      pure (some n, fr1, m1)

def evalSaltOpt : Nat → Frame → Machine → Option Expr → IM (Option ByteArray × Frame × Machine)
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | none => pure (none, fr, m)
    | some e => do
      let (v, fr1, m1) ← evalExpr fuel fr m e
      let s ← liftOpt (saltBytes v)
      pure (some s, fr1, m1)

def evalExprs : Nat → Frame → Machine → List Expr → IM (List Value × Frame × Machine)
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | [] => pure ([], fr, m)
    | e :: es => do
      let (v, fr1, m1) ← evalExpr fuel fr m e
      let (vs, fr2, m2) ← evalExprs fuel fr1 m1 es
      pure (v :: vs, fr2, m2)

def evalLValue : Nat → Frame → Machine → Expr → IM (LValue × Frame × Machine)
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | .ident x =>
      match fr.get? x with
      | some _ => pure (.local x, fr, m)
      | none =>
        match fc.var? x with
        | some v =>
          match v.mutability with
          | .mutable => pure (.storage ⟨v.key, []⟩ v.ty, fr, m)
          | .immutable => pure (.local (immName x), fr, m)
          | .constant => failure
        | none => failure
    | .member e f => do
      let (v, fr1, m1) ← evalExpr fuel fr m e
      match v with
      | .storageRef er ty =>
        let (er', fty) ← liftOpt (storageField fc.types er ty f)
        pure (.storage er' fty, fr1, m1)
      | .memRef obj => pure (.memField obj f, fr1, m1)
      | _ => failure
    | .index e i => do
      let (base, fr1, m1) ← evalExpr fuel fr m e
      let (iv, fr2, m2) ← evalExpr fuel fr1 m1 i
      match base with
      | .storageRef er ty =>
        let (er', ty') ← liftOp (storageIndex cfg fc.types m2.evm m2.heap er ty iv)
        pure (.storage er' ty', fr2, m2)
      | .memRef obj =>
        let n ← liftOpt (natOperand iv)
        let len ← liftOpt (memLength m2.heap obj)
        if n < len then pure (.memIndex obj n, fr2, m2) else throw (panicData 0x32)
      | _ => failure
    | _ => failure

def assignTuple : Nat → Frame → Machine → List (Option Expr) → List Value → IM (Frame × Machine)
  | 0, _, _, _, _ => failure
  | fuel+1, fr, m, a1, a2 => match a1, a2 with
    | [], [] => pure (fr, m)
    | none :: ls, _ :: vs => assignTuple fuel fr m ls vs
    | some l :: ls, v :: vs => do
      let (lv, fr1, m1) ← evalLValue fuel fr m l
      let (fr2, m2) ← liftOp (assign cfg fc.types fr1 m1 lv v)
      assignTuple fuel fr2 m2 ls vs
    | _, _ => failure

def declareTuple : Nat → Frame → Machine → List (Option Param) → List Value → IM (Frame × Machine)
  | 0, _, _, _, _ => failure
  | fuel+1, fr, m, a1, a2 => match a1, a2 with
    | [], [] => pure (fr, m)
    | none :: bs, _ :: vs => declareTuple fuel fr m bs vs
    | some p :: bs, v :: vs => do
      let some x := p.name | failure
      let (fr1, m1) ← liftOp (declare cfg fc.types fr m p.ty p.loc x (some v))
      declareTuple fuel fr1 m1 bs vs
    | _, _ => failure

def execStmt : Nat → Frame → Machine → Stmt → IM ExecResult
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | .block ss => do
      let r ← execBlock fuel fr m ss
      pure (exitBlock fr r)
    | .varDecl ty loc x none => do
      let (fr', m') ← liftOp (declare cfg fc.types fr m ty loc x none)
      pure (.normal fr' m')
    | .varDecl ty loc x (some e) => do
      let (v, fr1, m1) ← evalExpr fuel fr m e
      let (fr2, m2) ← liftOp (declare cfg fc.types fr1 m1 ty loc x (some v))
      pure (.normal fr2 m2)
    | .tupleDecl binders rhs => do
      let (v, fr1, m1) ← evalExpr fuel fr m rhs
      let .tuple vs := v | failure
      let (fr2, m2) ← declareTuple fuel fr1 m1 binders vs
      pure (.normal fr2 m2)
    | .exprStmt e => do
      let (_, fr1, m1) ← evalExpr fuel fr m e
      pure (.normal fr1 m1)
    | .ite c t e => do
      let (cv, fr1, m1) ← evalExpr fuel fr m c
      match cv, e with
      | .bool true, _ => execStmt fuel fr1 m1 t
      | .bool false, some s => execStmt fuel fr1 m1 s
      | .bool false, none => pure (.normal fr1 m1)
      | _, _ => failure
    | .while c body => execLoop fuel fr m (some c) none body
    | .doWhile body c => do
      let r ← execStmt fuel fr m body
      match r with
      | .normal fr1 m1 | .continue fr1 m1 => execLoop fuel fr1 m1 (some c) none body
      | .break fr1 m1 => pure (.normal fr1 m1)
      | .returned fr1 m1 => pure (.returned fr1 m1)
      | .reverted d => throw d
    | .for init c post body => do
      match init with
      | none => execLoop fuel fr m c post body
      | some s =>
        let r ← execStmt fuel fr m s
        match r with
        | .normal fr1 m1 => do
          let r ← execLoop fuel fr1 m1 c post body
          pure (exitBlock fr r)
        | .reverted d => throw d
        | _ => failure
    | .break => pure (.break fr m)
    | .continue => pure (.continue fr m)
    | .return none => pure (.returned fr m)
    | .return (some e) => do
      let (v, fr1, m1) ← evalExpr fuel fr m e
      match fr.retVars with
      | [r] =>
        let (fr2, m2) ← liftOp (assign cfg fc.types fr1 m1 (.local r) v)
        pure (.returned fr2 m2)
      | rs =>
        guard' (rs.length ≥ 2)
        let .tuple vs := v | failure
        let (fr2, m2) ← assignTuple fuel fr1 m1 (rs.map fun r => some (.ident r)) vs
        pure (.returned fr2 m2)
    | .emit (.ident ev) args => do
      let ei ← liftOpt (fc.event? ev)
      let es ← liftOpt (argExprs (ei.decl.params.map (·.name)) args)
      let (vs, fr1, m1) ← evalExprs fuel fr m es
      let (svs, m2) ← liftOp (abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) vs)
      let le ← liftOpt (mkLogEntry m2.this ei svs)
      pure (.normal fr1 (m2.pushLog le))
    | .revert (.ident err) args => do
      let ei ← liftOpt (fc.error? err)
      let es ← liftOpt (argExprs (paramNames ei.decl.params) args)
      let (vs, _, m1) ← evalExprs fuel fr m es
      let (svs, _) ← liftOp (abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) vs)
      let d ← liftOpt (customErrorData ei.sigStr ei.sig.paramTypes svs)
      throw d
    | .unchecked ss => do
      let r ← execBlock fuel { fr with unchecked := true } m ss
      pure (exitBlock fr (restoreUnchecked fr.unchecked r))
    | .placeholder => do
      let r ← execChain fuel (popFrame fr) m fr.chain fr.body
      liftOpt (settlePlaceholder fr r)
    | .tryCatch call ps body cs =>
      match call with
      | .call (.member recv f) opts args => do
        guard' (!(memberCallDirect fc fr recv))
        let (rv, fr1, m1) ← evalExpr fuel fr m recv
        match rv with
        | .contract c a =>
          let value ← evalValueOpt fuel fr1 m1 (valueOpt opts)
          let gasReq ← evalGasOpt fuel value.2.1 value.2.2 (gasOpt opts)
          let (fr3, m3) := (gasReq.2.1, gasReq.2.2)
          let es ← liftOpt (argExprsAny args)
          let (vs, fr4, m4) ← evalExprs fuel fr3 m3 es
          let d ← liftOpt (resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs)
          if d.returns.isEmpty && codeSize m4.evm a = 0 then throw ByteArray.empty
          let (sigStr, ptys, rtys) ← liftOpt (externalSig fc.types d)
          let (svs, m5) ← liftOp (abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs)
          let bs ← liftOpt (ABI.encodeABIValues? ptys svs)
          let perm := m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure
          let (z, m6, out) := callViaEVM o m5 a value.1 (selectorOf sigStr ++ bs.toByteArray) perm
            (calleeGas o m5 gasReq.1 value.1)
          if z then
            match tryRets cfg fc.types m6 ps rtys out with
            | some (rets, m7) =>
              let (fr5, m8) ← liftOp (bindTryParams cfg fc.types fr4 m7 ps rets)
              let r ← execBlock fuel fr5 m8 body
              pure (exitBlock fr r)
            | none => throw ByteArray.empty
          else
            match selectCatch cfg m6 cs out with
            | some (cc, cvs, m7) =>
              let (fr5, m8) ← liftOp (bindTryParams cfg fc.types fr4 m7 (catchParams cc) cvs)
              let r ← execBlock fuel fr5 m8 (catchBody cc)
              pure (exitBlock fr r)
            | none => throw out
        | _ => failure
      | .call (.new ty) opts args =>
        match newContract? fc ty with
        | some (c, tys) => do
          let value ← evalValueOpt fuel fr m (valueOpt opts)
          let salt ← evalSaltOpt fuel value.2.1 value.2.2 (saltOpt opts)
          let es ← liftOpt (argExprsAny args)
          let (vs, fr3, m3) ← evalExprs fuel salt.2.1 salt.2.2 es
          let (svs, m4) ← liftOp (abiArgs cfg fc.types m3 tys vs)
          let (a, m5, z, out) ← liftOpt (newViaEVM cfg o m4 c value.1 svs salt.1)
          if z then
            let (fr4, m6) ← liftOp (bindTryParams cfg fc.types fr3 m5 ps (if ps.isEmpty then [] else [.contract c a]))
            let r ← execBlock fuel fr4 m6 body
            pure (exitBlock fr r)
          else
            match selectCatch cfg m5 cs out with
            | some (cc, cvs, m6) =>
              let (fr4, m7) ← liftOp (bindTryParams cfg fc.types fr3 m6 (catchParams cc) cvs)
              let r ← execBlock fuel fr4 m7 (catchBody cc)
              pure (exitBlock fr r)
            | none => throw out
        | none => failure
      | _ => failure
    | _ => failure

def execLoop : Nat → Frame → Machine → Option Expr → Option Expr → Stmt → IM ExecResult
  | 0, _, _, _, _, _ => failure
  | fuel+1, fr, m, c, post, body => do
    let cond ← match c with
      | none => pure (true, fr, m)
      | some ce => do
        let (cv, fr1, m1) ← evalExpr fuel fr m ce
        match cv with
        | .bool b => pure (b, fr1, m1)
        | _ => failure
    let (b, fr1, m1) := cond
    if !b then return .normal fr1 m1
    execLoopBody fuel fr1 m1 c post body

/-- After a true loop condition: the body, the post-expression, and the next iteration. -/
def execLoopBody : Nat → Frame → Machine → Option Expr → Option Expr → Stmt → IM ExecResult
  | 0, _, _, _, _, _ => failure
  | fuel+1, fr1, m1, c, post, body => do
    let r ← execStmt fuel fr1 m1 body
    match r with
    | .normal fr2 m2 | .continue fr2 m2 =>
      let (fr3, m3) ← match post with
        | none => pure (fr2, m2)
        | some pe => do let (_, fr3, m3) ← evalExpr fuel fr2 m2 pe; pure (fr3, m3)
      execLoop fuel fr3 m3 c post body
    | .break fr2 m2 => pure (.normal fr2 m2)
    | .returned fr2 m2 => pure (.returned fr2 m2)
    | .reverted d => throw d

def execBlock : Nat → Frame → Machine → List Stmt → IM ExecResult
  | 0, _, _, _ => failure
  | fuel+1, fr, m, a1 => match a1 with
    | [] => pure (.normal fr m)
    | s :: ss => do
      let r ← execStmt fuel fr m s
      match r with
      | .normal fr1 m1 => execBlock fuel fr1 m1 ss
      | .reverted d => throw d
      | r => pure r

def execChain : Nat → Frame → Machine → List ModifierInvocation → Block → IM ExecResult
  | 0, _, _, _, _ => failure
  | fuel+1, fr, m, a1, a2 => match a1, a2 with
    | [], body => execBlock fuel fr m body
    | mi :: rest, body =>
      match fc.modifier? mi.name with
      | some md => do
        let es ← liftOpt (argExprs (paramNames md.decl.params) (mi.args.getD (.positional [])))
        let (vs, fr1, m1) ← evalExprs fuel fr m es
        let (fr2, m2) ← liftOp (bindModParams cfg fc.types (pushScope md.declaredIn fr1 rest body) m1 md.decl.params vs)
        let some mb := md.decl.body | failure
        let r ← execBlock fuel fr2 m2 mb
        pure (popScope r)
      | none =>
        if fc.linearization.contains mi.name then execChain fuel fr m rest body else failure

/-- Run a function in a fresh frame; returns its return values and the machine. -/
def callFn : Nat → Frame → Machine → FnDef → List Value → IM (List Value × Machine)
  | 0, _, _, _, _ => failure
  | fuel+1, _fr, m, fn, args => do
    let (fr0, m0) ← liftOp (enterFn cfg fc.types fn.declaredIn fn.decl args m)
    let some body := fn.decl.body | failure
    let r ← execChain fuel { fr0 with chain := fn.decl.modifiers, body := body } m0 fn.decl.modifiers body
    match r with
    | .reverted d => throw d
    | r =>
      let (fr2, m2) ← liftOpt (finished r)
      let rets ← liftOpt (retVals fr2)
      pure (rets, m2)

end

/-! ## Entry points -/

/-- One message call (mirrors `solidityExec`). -/
def interpExec (fuel : Nat) (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : IM (TopResult × Refinement.ReturnConvention) := do
  match selectorDispatch fc I.calldata with
  | some e =>
    let fn ← liftOpt fc.fns[e.fn]?
    let retTys ← liftOpt (returnAbiTys fc.types fn.decl)
    if fn.decl.mutability != .payable && I.weiValue != ⟨0⟩ then
      return (.reverted ByteArray.empty, .abi retTys)
    let svs ← liftOpt (decodeArgs cfg fc.types fn.decl I.calldata)
    let (vs, h0) ← liftOpt (ofAbiList fc.types (fn.decl.params.map (·.ty)) svs {})
    let m0 := initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0
    match (callFn cfg o fc fuel (rootFrame fc) m0 fn vs : Option (Except ByteArray _)) with
    | some (.ok (rets, m')) =>
      let out ← liftOpt (rets.mapM (toAbi m'.heap fuelDefault))
      pure (.returned m' out, .abi retTys)
    | some (.error d) => pure (.reverted d, .abi retTys)
    | none => failure
  | none =>
    if I.calldata.size == 0 && fc.receive?.isSome then
      let fid ← liftOpt fc.receive?
      let fn ← liftOpt fc.fns[fid]?
      let m0 := initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      match (callFn cfg o fc fuel (rootFrame fc) m0 fn [] : Option (Except ByteArray _)) with
      | some (.ok (_, m')) => pure (.returned m' [], .abi [])
      | some (.error d) => pure (.reverted d, .abi [])
      | none => failure
    else
      let fid ← liftOpt fc.fallback?
      let fn ← liftOpt fc.fns[fid]?
      if fn.decl.mutability != .payable && I.weiValue != ⟨0⟩ then
        return (.reverted ByteArray.empty, fallbackConvention fn.decl)
      let (vs, h0) ← liftOpt (fallbackArgs fn.decl I.calldata {})
      let m0 := initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0
      match (callFn cfg o fc fuel (rootFrame fc) m0 fn vs : Option (Except ByteArray _)) with
      | some (.ok (rets, m')) =>
        let out ← liftOpt (rets.mapM (toAbi m'.heap fuelDefault))
        pure (.returned m' out, fallbackConvention fn.decl)
      | some (.error d) => pure (.reverted d, fallbackConvention fn.decl)
      | none => failure

/-- Whether the spec rejects the calldata (no dispatch or undecodable arguments): the
    counterpart of the relation's `noDispatch`/`decodingFailed` cases. -/
def specRejectsB (I : Ethereum.ExecutionEnv) : Bool :=
  if !(dispatches fc I.calldata) then true
  else match selectorDispatch fc I.calldata with
    | some e =>
      match fc.fns[e.fn]? with
      | some fn => (fn.decl.mutability == .payable || I.weiValue == ⟨0⟩) && (decodeArgs cfg fc.types fn.decl I.calldata).isNone
      | none => false
    | none => false

/-- One state-variable initializer of the constructor. -/
def initStep (fuel : Nat) (acc : Frame × Machine) (v : FlatVar) : IM (Frame × Machine) := do
  let some e := v.init | failure
  let (val, fr1, m1) ← evalExpr cfg o fc fuel acc.1 acc.2 e
  match v.mutability with
  | .mutable => liftOp (assign cfg fc.types fr1 m1 (.storage ⟨v.key, []⟩ v.ty) val)
  | .immutable => liftOp (assign cfg fc.types fr1 m1 (.local (immName v.name)) val)
  | .constant => failure

/-- Arguments of a constructor-chain step: the decoded ones for the most-derived contract, the
    written base arguments (evaluated in the most-derived constructor's frame) otherwise. -/
def ctorArgsOf (fuel : Nat) (frP : Frame) (topArgs : List Value) (m : Machine) (step : CtorStep) :
    IM (List Value × Machine) :=
  if step.contract == fc.name then pure (topArgs, m)
  else match step.args with
    | none => pure ([], m)
    | some (_, a) => do
      let es ← liftOpt (argExprsAny a)
      let (vs, _, m1) ← evalExprs cfg o fc fuel frP m es
      pure (vs, m1)

/-- One step of the constructor chain (`imm_` locals threaded through `acc.2`). -/
def ctorStep (fuel : Nat) (frP : Frame) (topArgs : List Value) (acc : Machine × Store) (step : CtorStep) :
    IM (Machine × Store) := do
  match step.fn with
  | none => pure acc
  | some fid =>
    let fn ← liftOpt fc.fns[fid]?
    let (vs, m1) ← ctorArgsOf cfg o fc fuel frP topArgs acc.1 step
    let (fr2, m2) ← liftOp (enterFn cfg fc.types fn.declaredIn fn.decl vs m1 acc.2)
    let some body := fn.decl.body | failure
    let r ← execChain cfg o fc fuel { fr2 with chain := fn.decl.modifiers, body := body } m2 fn.decl.modifiers body
    let (fr4, m4) ← liftOpt (finished r)
    pure (m4, immStore fr4)

/-- Boolean `ctorPayable`. -/
def ctorPayableB (fc : FlatContract) (I : Ethereum.ExecutionEnv) : Bool :=
  match topCtor? fc with
  | some f => f.decl.mutability == .payable || I.weiValue == ⟨0⟩
  | none => I.weiValue == ⟨0⟩

/-- Construction (mirrors `solidityCtorExec`). -/
def interpCtor (fuel : Nat) (args : List ABI.ABIValue)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : IM CtorResult := do
  if !ctorPayableB fc I then return .reverted ByteArray.empty
  let imms0 ← liftOpt (immZero fc)
  let ptys := ((topCtor? fc).map (·.decl.params.map (·.ty))).getD []
  let (topArgs, h0) ← liftOpt (ofAbiList fc.types ptys args {})
  let m0 := initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0
  let (frP, m1) ← liftOp (ctorParamFrame cfg fc topArgs m0 imms0)
  let (frP1, m2) ← (initializers fc).foldlM (initStep cfg o fc fuel) (frP, m1)
  let (m3, imms) ← fc.ctorChain.foldlM (ctorStep cfg o fc fuel frP1 topArgs) (m2, immStore frP1)
  pure (.ok m3 imms)

end Interp

end Solidity
