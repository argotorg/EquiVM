import Examples.Caller.Bytecode
import Examples.Caller.Spec
import Reasoning.ABI
import Reasoning.EVMWord
import Reasoning.Theory
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.Stepping
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.Reach
import Reasoning.ExternalCall

/-!
# Caller — runtime-equivalence proof for `run(address t, uint256 n)`

`run` makes an **external call** `t.pow2(n)` and stores the result in `stored`.  The external call
is *opaque*: nothing is assumed about the code at `t`.  The EVM `CALL` and the Solm `externalCall`
invoke the identical `Θ`, so the opaque `(z, σ', o)` coincide on both sides by construction; the
success branch then stores `decode(o)` (EVM `SSTORE` ↔ Solm `.assign`).  Built on `RD.call`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

namespace Caller

/-! ## Solm-side dispatch facts (mirror `Truth`) -/

/-- Single-selector dispatch bundle (via `callerSelectorBytes`): `.eq` is the 4-byte
    calldata-prefix comparison, `.none_short` / `.none_nomatch` the no-dispatch cases. -/
theorem callerDispatch :
    SingleSelectorDispatch callerContract runTransition ⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ :=
  singleSelectorDispatch rfl callerSelectorBytes rfl


/-- **The Solm body stores the decoded result.**  With zero call value, the decoded `t ↦ address`,
    `n ↦ int`, a *successful* external call (`z = true`) whose return decodes to `value`, and the
    storage assign succeeding, `run`'s body runs to completion (`returned … none`), leaving the
    `stored` slot written. -/
theorem callerBodySuccess (evm : EVM.State) (locals : Solm.Store) {tval : EVM.Address} {nval : ℤ}
    {value : Value} {evm' evm'' : EVM.State} {out : ByteArray} {solm'' : Frame}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ht : locals.get? "t" = some (.address tval))
    (hn : locals.get? "n" = some (.int nval))
    (hcall : typedCallViaEVM callerConfig evm (EVM.address tval) "pow2" 0 [.int nval]
              (true, evm', out))
    (hdec : callerConfig.externalABI.decode? "pow2" out = some value)
    (hassign : assignStorageRef? callerConfig
        { contract := callerContract, locals := locals.insert "tmp" value } evm'
        .storage { base := "stored", steps := [] } value = .ok (solm'', evm'')) :
    ExecTransitionBody callerConfig callerContract evm locals runTransition.body
      (.returned solm'' evm'' none) := by
  refine ExecFuncBody.execBlockOK
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
      (ExecBlock.consNormal (ExecStmt.externalCallSuccess ?_ ?_ ?_ hcall hdec)
        (ExecBlock.consNormal (ExecStmt.assign ?_ hassign) ExecBlock.nil)))
  · show evalExpr? callerConfig _ evm (.var "t") = .ok (.address tval)
    simp only [evalExpr?, EvalResult.ofOption, ht]
  · show evalExpr? callerConfig _ evm (.intLit 0) = .ok (.int 0)
    simp only [evalExpr?]; rfl
  · show evalExprs? callerConfig _ evm [.var "n"] = .ok [.int nval]
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hn, EvalResult.bind, bind, pure]
  · show evalExpr? callerConfig { contract := callerContract, locals := locals.insert "tmp" value }
          evm' (.var "tmp") = .ok value
    simp only [evalExpr?, EvalResult.ofOption, store_get_self]

/-- **The Solm body reverts on a failed sub-call** (`z = false`): `require` passes, the external call
    fails, so the body reverts (`externalCallFailure`). -/
theorem callerBodyExtFail (evm : EVM.State) (locals : Solm.Store) {tval : EVM.Address} {nval : ℤ}
    {evm' : EVM.State} {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ht : locals.get? "t" = some (.address tval))
    (hn : locals.get? "n" = some (.int nval))
    (hcall : typedCallViaEVM callerConfig evm (EVM.address tval) "pow2" 0 [.int nval]
              (false, evm', out)) :
    ExecTransitionBody callerConfig callerContract evm locals runTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
      (ExecBlock.consRevert (ExecStmt.externalCallFailure ?_ ?_ ?_ hcall)))
  · show evalExpr? callerConfig _ evm (.var "t") = .ok (.address tval)
    simp only [evalExpr?, EvalResult.ofOption, ht]
  · show evalExpr? callerConfig _ evm (.intLit 0) = .ok (.int 0)
    simp only [evalExpr?]; rfl
  · show evalExprs? callerConfig _ evm [.var "n"] = .ok [.int nval]
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hn, EvalResult.bind, bind, pure]

/-- **The Solm body reverts on an under-length return** (`z = true`, `decode? = none`): `require`
    passes, the sub-call succeeds but its return data does not decode, so the body reverts
    (`externalCallReturnDecodeRevert`) — the spec analogue of the solc decoder's `< 32` revert. -/
theorem callerBodyDecodeRevert (evm : EVM.State) (locals : Solm.Store) {tval : EVM.Address} {nval : ℤ}
    {evm' : EVM.State} {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ht : locals.get? "t" = some (.address tval))
    (hn : locals.get? "n" = some (.int nval))
    (hcall : typedCallViaEVM callerConfig evm (EVM.address tval) "pow2" 0 [.int nval]
              (true, evm', out))
    (hdec : callerConfig.externalABI.decode? "pow2" out = none) :
    ExecTransitionBody callerConfig callerContract evm locals runTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert ?_ ?_ ?_ hcall hdec)))
  · show evalExpr? callerConfig _ evm (.var "t") = .ok (.address tval)
    simp only [evalExpr?, EvalResult.ofOption, ht]
  · show evalExpr? callerConfig _ evm (.intLit 0) = .ok (.int 0)
    simp only [evalExpr?]; rfl
  · show evalExprs? callerConfig _ evm [.var "n"] = .ok [.int nval]
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hn, EvalResult.bind, bind, pure]

/-! ## JUMPDEST membership facts -/

theorem callerContains15 : (D_J callerBytecode 0).contains ⟨15⟩ = true := by
  jump_dest
theorem callerContains41 : (D_J callerBytecode 0).contains ⟨41⟩ = true := by
  jump_dest
theorem callerContains45 : (D_J callerBytecode 0).contains ⟨45⟩ = true := by
  jump_dest

/-! ## Selector decode (generic instance) -/

/-- The EVM selector check `eq(0x381fd190, SHR(calldata,224))` agrees with the dispatcher's
    4-byte compare `0x381fd190 == calldata.extract 0 4`. -/
theorem callerEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨941609360⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x38 0x1f 0xd1 0x90 ⟨941609360⟩ (by decide)

theorem callerContains491 : (D_J callerBytecode 0).contains ⟨491⟩ = true := by
  jump_dest
theorem callerContains203 : (D_J callerBytecode 0).contains ⟨203⟩ = true := by
  jump_dest
theorem callerContains71 : (D_J callerBytecode 0).contains ⟨71⟩ = true := by
  jump_dest
theorem callerContains194 : (D_J callerBytecode 0).contains ⟨194⟩ = true := by
  jump_dest
theorem callerContains297 : (D_J callerBytecode 0).contains ⟨297⟩ = true := by
  jump_dest
theorem callerContains306 : (D_J callerBytecode 0).contains ⟨306⟩ = true := by
  jump_dest
theorem callerContains315 : (D_J callerBytecode 0).contains ⟨315⟩ = true := by
  jump_dest
theorem callerContains325 : (D_J callerBytecode 0).contains ⟨325⟩ = true := by
  jump_dest
theorem callerContains450 : (D_J callerBytecode 0).contains ⟨450⟩ = true := by
  jump_dest
theorem callerContains464 : (D_J callerBytecode 0).contains ⟨464⟩ = true := by
  jump_dest
theorem callerContains504 : (D_J callerBytecode 0).contains ⟨504⟩ = true := by
  jump_dest

/-! ## EVM traces (revert scenarios) -/

/-- `callvalue ≠ 0`: the non-payable guard reverts (prologue → not-taken JUMPI → revert stub). -/
theorem callerX_callvalue_ne
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiNT (isZero_eq_zero_of_ne hwv),
      raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- The shared dispatcher prefix for `callvalue = 0`: through the non-payable guard's taken jump
    (`0x08 → 0x0f`) and on to the `0x18` (24) `JUMPI`, reaching pc 24 with stack `[41, size < 4]`. -/
theorem callerX_cvz_prefix
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
        [⟨41⟩, UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 14 53 := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiT (by rw [hwv]; decide) callerContains15,
      jumpdest, pop, push1 ⟨4⟩, calldatasize, lt, push2 ⟨41⟩ ]

/-! ## Dispatch machinery (single arm) — generic `Reasoning.Reach`/`Solc` driver -/

/-- The 4-byte selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev callerSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- `run`'s single selector arm begins at pc 30 (`DUP1; PUSH4 0x381fd190; EQ; PUSH2 0x2d; JUMPI`). -/
abbrev callerFirstArmPc : UInt256 := ⟨30⟩

/-- The lone selector arm is well-formed (`DUP1; PUSH4; EQ; PUSH2; JUMPI`). -/
theorem callerArmWellFormed : armWellFormed callerBytecode callerFirstArmPc :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The arm's `PUSH4` selector value is `0x381fd190`. -/
theorem callerArmSelNat : armSelNat callerBytecode callerFirstArmPc = ⟨941609360⟩ := by decide

/-- **Selector coupling.**  Arm 0's `EQ` (its `PUSH4` value vs the calldata selector word) is `1`/`0`
    exactly as `0x381fd190` matches `calldata[0:4]` — the table-indexed instance of `callerEvmSelector`. -/
theorem callerMatch_eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (armSelNat callerBytecode callerFirstArmPc) (callerSelWord I)
      = if ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  rw [callerArmSelNat]; exact callerEvmSelector hsz

/-- **Machinery driver (proven).**  `cv = 0`, `size ≥ 4`, matching selector: prologue → callvalue
    guard → calldata-ok → selector load → `RD.dispatchTo` over the single arm, reaching the `run`
    dispatch body entry at pc 45 with the selector word on the stack. -/
theorem callerReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨45⟩
        [callerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := callerFirstArmPc) (bodyPC := ⟨45⟩) (i := 0)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => by rw [Nat.le_zero.mp hj]; exact callerArmWellFormed)
    (fun j hj => absurd hj (by omega))
    (by show UInt256.eq (armSelNat callerBytecode callerFirstArmPc) (callerSelWord I) ≠ ⟨0⟩
        rw [callerMatch_eq I hsz, if_pos hmatch]; decide)
    (by jump_dest) (by decide)

/-- `callvalue = 0 ∧ calldatasize < 4`: the prefix's `JUMPI` jumps to the `0x29` (41) revert stub. -/
theorem callerX_cvz_short
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (callerX_cvz_prefix hcode hwv) with [
    jumpiT (lt_four_ne_zero_of_lt hsz) callerContains41,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- `calldatasize ≥ 4, wrong selector`: fall through the size JUMPI, decode/compare the selector
    (`EQ = 0`), and revert at `0x29` (41). -/
theorem callerX_cvz_revertB
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (callerX_cvz_prefix hcode hwv) with [
    jumpiNT (lt_four_eq_zero_of_ge hsz hsize),
    push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨941609360⟩, eq, push2 ⟨45⟩,
    jumpiNT (by rw [show ((⟨0⟩ : UInt256).toNat) = 0 from by decide, callerEvmSelector hsz];
                simp [hmatch]),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ## Success path — the dispatcher reaches the `run` dispatch at pc 45 -/

theorem callerContains348 : (D_J callerBytecode 0).contains ⟨348⟩ = true := by
  jump_dest

/-- **run-dispatch (pc 45 → arg-decoder entry pc 348).**  Pushes the two return addresses
    (`0x42 = 66` after decode, `0x47 = 71` after body), sets up `[headStart=4, dataEnd]`, and jumps
    into solc's `abi_decode_tuple_(address,uint256)` at pc 348. -/
theorem callerX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨348⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, rd0⟩ := callerReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  have rd := evm_run rd0 with [
    jumpdest, push2 ⟨71⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1, push2 ⟨66⟩,
    swap2, swap1, push2 ⟨348⟩,
    jump callerContains348 ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz) hsize] at rd
  exact ⟨_, _, rd⟩

/-! ## The opaque-call coincidence (the conceptual crux)

The EVM `CALL` (via `RD.call`) and the Solm `externalCall` (via `typedCallViaEVM`) invoke the
*identical* `Θ`, so the opaque result coincides on both sides by construction — no assumption about
the callee's code.  This is now the **generic** `Reasoning.Theory.callCoincides` (and the
depth-limit `callNotMade_depthLimit`) in `Reasoning/ExternalCall.lean`; `Caller` only supplies the
trace couplings (`callerTarget_eq`, `callerEncode_eq`). -/

/-! ## Decoder trace (abi_decode (address,uint256)) -/

/-- All `callerBytecode` jump targets validated by one tactic (mirrors `callerContains15`). -/
macro "caller_jd" : term => `(by jump_dest)

/-- Decoder segment: bounds-check (`datalen ≥ 64`) passes, set up arg0 offset, jump to the address
    element decoder at pc 277.  Counters existential. -/
theorem callerX_dec277 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨277⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨k0, C0, rd0⟩ := callerX_toDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  exact ⟨_, _, evm_run rd0 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push2 ⟨370⟩,
    jumpiT (by rw [hslt]; decide) caller_jd,
    jumpdest, push0, push2 ⟨383⟩, dup6, dup3, dup7, add, push2 ⟨277⟩,
    jump caller_jd ]⟩

/-- Address-mask literal (`PUSH20 0xff…ff`). -/
def addrMask : UInt256 := ⟨1461501637330902918203684832716283019655932542975⟩

/-- Decoder segment: load + cleanup arg0 (address), reaching the clean-address check at pc 264.
    `tw` is the raw calldata word at offset 4, `tc = tw & addrMask` the cleaned address. -/
theorem callerX_dec264 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨264⟩
        [UInt256.land (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)) addrMask,
          uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32),
          ⟨291⟩, uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32),
          ⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec277 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨291⟩, dup2, push2 ⟨255⟩, jump caller_jd,
    jumpdest, push2 ⟨264⟩, dup2, push2 ⟨238⟩, jump caller_jd,
    jumpdest, push0, push2 ⟨248⟩, dup3, push2 ⟨207⟩, jump caller_jd,
    jumpdest, push0, push20 addrMask, dup3, and, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, swap1, pop, swap2, swap1, pop, jump caller_jd ]⟩

/-- The decoded calldata address word at offset 4. -/
abbrev callerArg0 (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- Decoder segment: the clean-address check passes (`address` canonical), return to pc 291. -/
theorem callerX_dec291 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨291⟩
        [callerArg0 I, ⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec264 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨274⟩, jumpiT (by rw [hclean]; decide) caller_jd,
    jumpdest, pop, jump caller_jd ]⟩

theorem ueq_self (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  have h : UInt256.eq a a = UInt256.ofNat 1 := by simp [UInt256.eq, UInt256.fromBool]
  rw [h]; rfl

/-- The decoded calldata uint256 word at offset 36. -/
abbrev callerArg1 (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

/-- **Calldata decode for `run(address t, uint256 n)`.**  With ≥ 68 bytes of calldata and a
    *canonical* address argument, decoding succeeds, binding `t`/`n` to the EVM's words at offsets
    4 / 36 — the Solm-side analogue of the bytecode's ABI decoder. -/
theorem callerDecode_n {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (callerArg0 I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata
      = some (((∅ : Solm.Store).insert "t"
          (.address (Ethereum.AccountAddress.ofNat (callerArg0 I).toNat))).insert "n"
          (.int (Int.ofNat (callerArg1 I).toNat))) := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, calldataWord, callerArg0, callerArg1]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "t") (y := "n") hsz68 hbig hcanon

theorem callerDecode_none_short {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short
      (cd := I.calldata) (x := "t") (y := "n") hsz4 hshort

theorem callerDecode_none_noncanon {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (callerArg0 I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, callerArg0]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "t") (y := "n") hsz68 hbig hnc

theorem callerDecode_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge
      (cd := I.calldata) (x := "t") (y := "n") hbig

/-- Decoder final segment: decode arg1 (uint256), return to the dispatch point pc 66 with the two
    decoded values `[n, t, 71, sel]` on the stack. -/
theorem callerX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨66⟩
        [callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec291 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨400⟩, dup6, dup3, dup7, add, push2 ⟨328⟩, jump caller_jd,
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨342⟩, dup2, push2 ⟨306⟩, jump caller_jd,
    jumpdest, push2 ⟨315⟩, dup2, push2 ⟨297⟩, jump caller_jd,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, dup2, eq, push2 ⟨325⟩, jumpiT (by rw [ueq_self]; decide) caller_jd,
    jumpdest, pop, jump caller_jd,
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump caller_jd ]⟩

/-! ## Body trace: encode `pow2(n)` calldata, reach the CALL -/

/-- Body segment: clean the target address, load the free pointer, build the selector word; reach
    the first `MSTORE` (selector → mem[128]) at pc 117. -/
theorem callerX_body117 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨117⟩
        [⟨128⟩, UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1143701499⟩) ⟨224⟩, ⟨128⟩, callerArg1 I,
          ⟨1143701499⟩, UInt256.land addrMask (callerArg0 I), callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_decoded hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨73⟩, jump caller_jd,
    jumpdest, dup2, push20 addrMask, and, push4 ⟨1143701499⟩, dup3, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2 ]⟩

/-- Memory after writing the (left-shifted) `pow2` selector to `mem[128]`. -/
noncomputable def callerSelMem : ByteArray :=
  (UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1143701499⟩) ⟨224⟩).toByteArray.write 0
    solcFreePtrMem 128 32

/-- Body segment: store the selector, set up the encoder call, jump to the uint256 encoder at pc 425. -/
theorem callerX_body425 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨425⟩
        [⟨4⟩ + ⟨128⟩, callerArg1 I, ⟨130⟩, ⟨1143701499⟩, UInt256.land addrMask (callerArg0 I),
          callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        callerSelMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_body117 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    raw mstore 6 callerSelMem (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨130⟩, swap2, swap1, push2 ⟨425⟩, jump caller_jd ]⟩

/-- Memory after the encoder writes `n` at mem[132] (the full `pow2(n)` calldata at mem[128..164]). -/
noncomputable def callerCalldataMem (I : ExecutionEnv) : ByteArray :=
  (callerArg1 I).toByteArray.write 0 callerSelMem 132 32

/-- The free-memory pointer the body MLOADs at offset 64 (carried symbolically; provably `⟨128⟩`). -/
noncomputable def callerOutPtr (I : ExecutionEnv) : UInt256 :=
  if (⟨64⟩ : UInt256).toNat ≥ (callerCalldataMem I).size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩
  then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian ((callerCalldataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))

/-- `callerSelMem` is exactly the generic solc "store a word at `0x80`" memory (`solcReturnMem`)
    applied to the shifted selector, so its size / read-backs are the generic ones. -/
theorem callerSelMem_size : callerSelMem.size = 160 := solcReturnMem_size _

theorem callerSelMem_read64 : callerSelMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcReturnMem_read64 _

/-- The full `pow2(n)` calldata buffer is 164 bytes (`0x80 .. 0xa4`). -/
theorem callerCalldataMem_size (I : ExecutionEnv) : (callerCalldataMem I).size = 164 := by
  unfold callerCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, callerSelMem_size, toByteArray_size]
  omega

/-- The free pointer (`mem[0x40]`) is untouched by the selector/arg writes: it still reads `0x80`. -/
theorem callerCalldataMem_read64 (I : ExecutionEnv) :
    (callerCalldataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold callerCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega)
        (by omega), callerSelMem_read64]

/-- **The output pointer the `CALL` uses is `0x80`** — the byte-level coupling that ties the decoder's
    read region to the `CALL` out-region. -/
theorem callerOutPtr_eq (I : ExecutionEnv) : callerOutPtr I = ⟨128⟩ := by
  unfold callerOutPtr
  exact mloadFreePtrValue (by rw [callerCalldataMem_size]; decide) (by decide)
    (callerCalldataMem_read64 I)

/-- `callerSelMem`'s bytes `[128:132]` are exactly the `pow2` selector — the high 4 bytes of the
    selector word `solc` `MSTORE`s at `0x80` (`selector << 224`). -/
theorem callerSelMem_selector : callerSelMem.extract 128 132 = pow2Selector := by
  rw [show callerSelMem
        = solcReturnMem (UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1143701499⟩) ⟨224⟩) from rfl,
      solcReturnMem_eq,
      extract_append_right_window _ _ _ _ (by rw [solcFreePtrMem_pad_size]),
      solcFreePtrMem_pad_size, show (128:ℕ) - 128 = 0 from rfl, show (132:ℕ) - 128 = 4 from rfl,
      toByteArray_eq_toBytesBE]
  native_decide

/-- **Encoding coupling (byte level).**  The 36 bytes the `CALL` sends (`mem[0x80 .. 0xa4]`) are
    exactly `selector ++ word(n)` — the selector in `[128:132]` and the argument word in `[132:164]`. -/
theorem callerCalldataMem_read128_36 (I : ExecutionEnv) :
    (callerCalldataMem I).readWithPadding 128 36 = pow2Selector ++ (callerArg1 I).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
        (by rw [callerCalldataMem_size]), callerCalldataMem,
      write32_eq _ callerSelMem 132 (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega)]
  have hAsz : (callerSelMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, callerSelMem_size]; omega
  have hBsz : ((callerArg1 I).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hPsz : (callerSelMem.extract 0 132 ++ (callerArg1 I).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : (callerArg1 I).toByteArray.extract 0 32 = (callerArg1 I).toByteArray := by
    have h := @ByteArray.extract_zero_size (callerArg1 I).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
      extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega), hAsz,
      extract_prefix _ 132 128 132 (by omega), callerSelMem_selector,
      extract_extract_BA, show (0:ℕ) + 0 = 0 from rfl,
      show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

/-- `wordOfInt (Int.ofNat a.toNat) = a` (a nonneg word round-trips through `ℤ`). -/
theorem wordOfInt_ofNat_toNat (a : UInt256) : EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

/-- **Encoding coupling (spec level).**  The Solm ABI's `encode? "pow2" [n]` produces exactly the
    36-byte buffer the bytecode sends to the `CALL`. -/
theorem callerEncode_eq (I : ExecutionEnv) :
    callerExternalABI.encode? "pow2" [.int (Int.ofNat (callerArg1 I).toNat)]
      = some ((callerCalldataMem I).readWithPadding 128 36) := by
  rw [callerCalldataMem_read128_36]
  show some (pow2Selector ++ UInt256.toByteArray (EVM.wordOfInt (Int.ofNat (callerArg1 I).toNat)))
      = some (pow2Selector ++ (callerArg1 I).toByteArray)
  rw [wordOfInt_ofNat_toNat]

/-- `Nat.land` is commutative (via testbits). -/
theorem natLandComm (a b : ℕ) : Nat.land a b = Nat.land b a := by
  apply Nat.eq_of_testBit_eq; intro i
  show (a &&& b).testBit i = (b &&& a).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

/-- `UInt256.land` is commutative. -/
theorem uland_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show (Fin.land a.val b.val).val = (Fin.land b.val a.val).val
  simp only [Fin.land]; rw [natLandComm]

/-- The clean-address mask is idempotent on a canonical argument: `addrMask & arg0 = arg0`. -/
theorem callerLand_target {I : ExecutionEnv}
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    UInt256.land addrMask (callerArg0 I) = callerArg0 I := by
  have heq : callerArg0 I = UInt256.land (callerArg0 I) addrMask := by
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hclean
    exact absurd hclean (by decide)
  rw [uland_comm, ← heq]

/-- **Target coupling.**  The decoded address (`AccountAddress.ofNat arg0`) is exactly the
    `CALL` target the bytecode masks (`AccountAddress.ofUInt256 (addrMask & arg0)`). -/
theorem callerTarget_eq {I : ExecutionEnv}
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    EVM.address (AccountAddress.ofNat (callerArg0 I).toNat)
      = AccountAddress.ofUInt256 (UInt256.land addrMask (callerArg0 I)) := by
  rw [callerLand_target hclean]
  apply Fin.ext
  show (callerArg0 I).toNat % EVM.addressModulus % AccountAddress.size
      = (callerArg0 I).val % AccountAddress.size % AccountAddress.size
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  rfl

/-- Body segment: run the uint256 encoder (MSTORE `n` at mem[132]), set up and MLOAD for the CALL,
    reaching the GAS at pc 142 (just before the `CALL`). -/
theorem callerX_toCall142 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨142⟩
        [UInt256.land addrMask (callerArg0 I), ⟨0⟩, callerOutPtr I,
          UInt256.sub ⟨164⟩ (callerOutPtr I), callerOutPtr I, ⟨32⟩, ⟨164⟩, ⟨1143701499⟩,
          UInt256.land addrMask (callerArg0 I), callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        (callerCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_body425 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨444⟩, push0, dup4, add, dup5,
    push2 ⟨410⟩, jump caller_jd,
    jumpdest, push2 ⟨419⟩, dup2, push2 ⟨297⟩, jump caller_jd,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, dup3,
    raw mstore 3 (callerCalldataMem I) (UInt256.ofNat 6) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, pop, jump caller_jd,
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload 0 (callerOutPtr I) (UInt256.ofNat 6) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8 ]⟩

/-- **The opaque CALL executes in the trace.**  GAS then `RD.call` (value 0): the result
    `(cA', σ', z, o)` is the *opaque* `Θ` output, and the run reaches the post-CALL `ISZERO` at pc 143
    with the success flag on the stack — no assumption about the callee's code. -/
theorem callerX_afterCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (mem' : ByteArray) (aw' : UInt256) (rdata' : ByteArray) (k' C' : ℕ),
      RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          ⟨164⟩ :: ⟨1143701499⟩ :: UInt256.land addrMask (callerArg0 I) :: callerArg1 I ::
          callerArg0 I :: ⟨71⟩ ::
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ :: [])
        mem' aw' rdata' (cA', σ') k' C' := by
  obtain ⟨k, C, rd142⟩ := callerX_toCall142 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  obtain ⟨gv, rd143⟩ := rd142.gas (by decide) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', _hΘ, rd144, _hosz⟩ :=
    rd143.call (by decide) hdepth (by evm_ov)
  exact ⟨cA', σ', z, _, _, _, k', C', rd144⟩

/-- **The opaque CALL, packaged for the assembly.**  Exposes the post-`CALL` `RD` cursor (memory and
    active-words resolved to their concrete `o.write …` / `⟨6⟩` forms) **together with** the Solm-side
    `typedCallViaEVM` fact built from the *same* `Θ`-link — the coincidence that lets the EVM and
    Solm sub-calls share `(z, σ', o)`. -/
theorem callerX_postCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (o : ByteArray)
      (A' : Substate) (k' C' : ℕ),
      RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          ⟨164⟩ :: ⟨1143701499⟩ :: UInt256.land addrMask (callerArg0 I) :: callerArg1 I ::
          callerArg0 I :: ⟨71⟩ ::
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ :: [])
        (o.write 0 (callerCalldataMem I) (callerOutPtr I).toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat) ⟨6⟩ o (cA', σ') k' C'
    ∧ typedCallViaEVM callerConfig (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat (callerArg0 I).toNat)) "pow2" 0
        [.int (Int.ofNat (callerArg1 I).toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' }, o)
    ∧ o.size < UInt256.size := by
  obtain ⟨k, C, rd142⟩ := callerX_toCall142 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  obtain ⟨gv, rd143⟩ := rd142.gas (by decide) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', _hΘ, rd144, hosz⟩ :=
    rd143.call (by decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := _hΘ
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, ?_⟩
  · -- the `RD` cursor: rewrite the active-words `M`-expression to `⟨6⟩`
    have haw : UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (callerOutPtr I).toNat (UInt256.sub ⟨164⟩ (callerOutPtr I)).toNat)
        (callerOutPtr I).toNat (⟨32⟩ : UInt256).toNat) = (⟨6⟩ : UInt256) := by
      rw [callerOutPtr_eq]; decide
    exact haw ▸ rd144
  · -- the Solm-side coincidence, fed the same `Θ`-link
    refine callCoincides (targetWord := UInt256.land addrMask (callerArg0 I))
      (mem := callerCalldataMem I) (inOff := callerOutPtr I)
      (inSize := UInt256.sub ⟨164⟩ (callerOutPtr I)) hperm
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (callerTarget_eq hclean) ?_ hΘ
    rw [show (callerOutPtr I).toNat = 128 from by rw [callerOutPtr_eq]; decide,
        show (UInt256.sub ⟨164⟩ (callerOutPtr I)).toNat = 36 from by rw [callerOutPtr_eq]; decide]
    exact callerEncode_eq I
  · exact hosz

/-- **Post-call failure tail** (`z = false`): the `CALL` returned `0`, so the solc check
    `iszero(success)` jumps into the `RETURNDATACOPY … REVERT` bail-out — the whole run reverts,
    independent of the (opaque) return data. -/
theorem callerX_postRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {rest : List UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨0⟩ :: rest) mem aw rdata acc k C)
    (hov : rest.length + 4 ≤ 1024) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- 144 ISZERO; 145 DUP1; 146 ISZERO; 147 PUSH2 158; 150 JUMPI (not taken, z = false)
  have rd151 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I)
      (⟨142⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
      (UInt256.isZero ⟨0⟩ :: rest) mem aw rdata acc _ _ :=
    evm_run rd with [iszero, dup1, iszero, push2 ⟨158⟩, jumpiNT (by decide)]
  -- 151 RETURNDATASIZE; 152 PUSH0; 153 PUSH0; 154 RETURNDATACOPY
  obtain ⟨mem2, aw2, k2, C2, rd155⟩ :=
    RD.returndatacopyFull rd151 (by decide) (by decide) (by decide) (by decide)
      (by simp only [List.length_cons]; omega)
  -- 155 RETURNDATASIZE; 156 PUSH0; 157 REVERT
  have rd156 := RD.returndatasize rd155 (by decide) (by simp only [List.length_cons]; omega)
  have rd157 := RD.push0 rd156 (by decide) (by simp only [List.length_cons]; omega)
  exact RD.rev _ rd157 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by simp only [List.length_cons]; omega)

theorem callerContains158 : (D_J callerBytecode 0).contains ⟨158⟩ = true := by
  jump_dest

/-- **Post-call success prefix** (`z = true`): the `CALL` returned `1`, so `iszero(success)` is
    false and control jumps to pc 158, the 4 dead stack words are `POP`ped, and `PUSH1 64` pushes the
    free-pointer slot address — reaching the `MLOAD` at pc 165 with stack `[64, arg1, arg0, 71, sel]`.
    (`d0 d1 d2` are the three dispatcher words above `arg1` that the `POP`s discard.) -/
theorem callerX_succ_to165 {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    {d0 d1 d2 : UInt256} {tl : List UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨1⟩ :: d0 :: d1 :: d2 :: tl) mem aw rdata acc k C)
    (hov : tl.length + 7 ≤ 1024) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨165⟩
        (⟨64⟩ :: tl) mem aw rdata acc k' C' := by
  -- 144 ISZERO; DUP1; ISZERO; PUSH2 158; JUMPI (taken, z = true) → 158; POP×4; PUSH1 64
  refine ⟨_, _, evm_run rd with [iszero, dup1, iszero, push2 ⟨158⟩,
    jumpiT (by decide) callerContains158, jumpdest, pop, pop, pop, pop, push1 ⟨64⟩]⟩

theorem callerContains470 : (D_J callerBytecode 0).contains ⟨470⟩ = true := by
  jump_dest

/-- The memory after the success decoder's free-pointer `MSTORE` at offset 64.  The result word at
    `[128, 160)` (where the CALL wrote `o`) is untouched, so `readWithPadding 128` is preserved. -/
noncomputable def callerMem2 (o mem : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
    (UInt256.lnot ⟨31⟩))).toByteArray.write 0 mem 64 32

/-- **Success decoder, straight-line part (165 → 470).**  `MLOAD` the free pointer (`fp = 128`),
    `RETURNDATASIZE` (= `|o|`), round up and bump the free pointer (`MSTORE` at `0x40`), compute
    `dataEnd = 128 + |o|`, and jump into the length-checking decoder subroutine at pc 470 — leaving
    `[128, 128+|o|, 194, …]` on the stack.  Active words stay `⟨6⟩`, so every memory op is free. -/
theorem callerX_succ_to470 {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨165⟩
            [⟨64⟩, arg1, arg0, ⟨71⟩, sel] mem ⟨6⟩ o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
          = ⟨128⟩) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
      (callerMem2 o mem) ⟨6⟩ o acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    raw mload 0 ⟨128⟩ ⟨6⟩ (by decide)
      mem_cost
      hfp (by decide) (by evm_ov),
    returndatasize,
    push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add, dup1, push1 ⟨64⟩,
    raw mstore 0 ((UInt256.add ⟨128⟩ (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
        (UInt256.lnot ⟨31⟩))).toByteArray.write 0 mem 64 32) ⟨6⟩ (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨194⟩, swap2, swap1, push2 ⟨470⟩, jump callerContains470 ]⟩

/-- **Success decoder, length check (470 → 491).**  `slt(dataEnd − headStart, 32) = slt(|o|, 32) = 0`
    (since `|o| ≥ 32`), so `iszero` is `1` and the `JUMPI` jumps past the bail-out to pc 491. -/
theorem callerX_succ_to491 {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
            [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o acc k C)
    (ho32 : 32 ≤ o.size) (ho : o.size < 2 ^ 255) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨491⟩
      [⟨0⟩, ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
      mem2 ⟨6⟩ o acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨491⟩,
    jumpiT (by rw [solcDecodeEndLenCheckOk_128_32 ho32 ho]; decide) callerContains491 ]⟩

/-- **Success-path under-length revert (470 → 203 REVERT).**  When `|o| < 32` the length check
    `slt(|o|, 32) = 1`, so `iszero` is `0`, the `JUMPI` is *not* taken, and control falls into the
    `…203 REVERT` bail-out ⇒ `RDrev` — matching Solm's `externalCallReturnDecodeRevert`. -/
theorem callerX_succ_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
            [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o acc k C)
    (ho : o.size < 32) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨491⟩,
    jumpiNT (by rw [solcDecodeEndLenCheckShort_128_32 ho]; decide),
    push2 ⟨490⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- **Success-path huge returndata revert (470 → 203 REVERT).**  When the return-data length has
    the sign bit set, solc's signed length check follows the same bail-out path as the short case. -/
theorem callerX_succ_revert_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
            [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o acc k C)
    (hhi : 2 ^ 255 ≤ o.size) (hlo : o.size < UInt256.size) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨491⟩,
    jumpiNT (by rw [solcDecodeEndLenCheckHuge_128_32 hhi hlo]; decide),
    push2 ⟨490⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- **Success decoder tail (491 → STOP).**  Mirrors the calldata `uint256` decoder
    (`callerX_decoded`), but reads the result word from **memory** (`MLOAD` at 453, coupled to the
    `CALL` out-region via `hword`) instead of calldata.  Threads the word through the no-op
    `uint256` validator (306/297/315/325), then `SSTORE`s it to slot 0 and `STOP`s ⇒
    `RDret (cA, σ[slot0 := word])`. -/
theorem callerX_succ_tail {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨491⟩
            [⟨0⟩, ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o (cAx, σx) k C)
    (hperm : I.perm = true)
    (hword : mem2.readWithPadding 128 32 = o.extract 0 32)
    (hsize2 : 128 < mem2.size) :
    RDret callerBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAx, sstoreAccountMap I.codeOwner σx ⟨0⟩
              (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))))
      ByteArray.empty := by
  have rd198 := evm_run rd with [
    jumpdest, push0, push2 ⟨504⟩, dup5, dup3, dup6, add, push2 ⟨450⟩, jump callerContains450,
    jumpdest, push0, dup2,
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) ⟨6⟩ (by decide)
      mem_cost
      (by
        have h128 : ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 := by decide
        split_ifs with h
        · exfalso; rcases h with h | h
          · rw [h128] at h; omega
          · exact absurd h (by decide)
        · rw [h128, hword])
      (by decide) (by evm_ov),
    swap1, pop, push2 ⟨464⟩, dup2, push2 ⟨306⟩, jump callerContains306,
    jumpdest, push2 ⟨315⟩, dup2, push2 ⟨297⟩, jump callerContains297,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump callerContains315,
    jumpdest, dup2, eq, push2 ⟨325⟩, jumpiT (by rw [ueq_self]; decide) callerContains325,
    jumpdest, pop, jump callerContains464,
    jumpdest, swap3, swap2, pop, pop, jump callerContains504,
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump callerContains194,
    jumpdest, push0, dup2, swap1 ]
  obtain ⟨k', C', rd199⟩ := rd198.sstore hperm (by decide) (by evm_ov)
  exact RD.stop (evm_run rd199 with [pop, pop, pop, jump callerContains71, jumpdest])
    (by decide) (by evm_ov)

/-- **The whole success decoder, chained (144 → STOP).**  Given the post-call cursor (`z = true`,
    active words `⟨6⟩`), the free-pointer read `hfp`, the result-region read `hword`, and the size
    bound, runs `165 → 470 → 491 → SSTORE → STOP` ⇒ `RDret (cA, σ[slot0 := decode o])`. -/
theorem callerX_successChain {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {mem : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel d0 d1 d2 : UInt256}
    (rd144 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨1⟩ :: d0 :: d1 :: d2 :: arg1 :: arg0 :: ⟨71⟩ :: sel :: []) mem ⟨6⟩ o (cAx, σx) k C)
    (hperm : I.perm = true) (ho32 : 32 ≤ o.size) (ho : o.size < 2 ^ 255)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
          = ⟨128⟩)
    (hword : mem.readWithPadding 128 32 = o.extract 0 32) (hmsz : 160 ≤ mem.size) :
    RDret callerBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAx, sstoreAccountMap I.codeOwner σx ⟨0⟩
              (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))))
      ByteArray.empty := by
  obtain ⟨k1, C1, rd165⟩ := callerX_succ_to165 rd144 (by simp)
  obtain ⟨k2, C2, rd470⟩ := callerX_succ_to470 rd165 hfp
  obtain ⟨k3, C3, rd491⟩ := callerX_succ_to491 rd470 ho32 ho
  have hword2 : (callerMem2 o mem).readWithPadding 128 32 = o.extract 0 32 := by
    rw [callerMem2, write32_read_above _ _ 64 128 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega), hword]
  have hmsz2 : 128 < (callerMem2 o mem).size := by
    rw [callerMem2, write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, toByteArray_size]
    omega
  exact callerX_succ_tail rd491 hperm hword2 hmsz2

/-- **The clean-address check ⇒ canonical address.**  The bytecode's `eq(arg0, arg0 & 0xff…ff)`
    holding means `arg0`'s high bits are zero, i.e. `arg0 < 2¹⁶⁰` — exactly the Solm decoder's
    address-validity condition. -/
theorem callerArg0_canonical {I : ExecutionEnv}
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    (callerArg0 I).toNat < EVM.addressModulus := by
  have heq : callerArg0 I = UInt256.land (callerArg0 I) addrMask := by
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hclean
    exact absurd hclean (by decide)
  have hlandle : ∀ a b : ℕ, Nat.land a b ≤ b := by
    intro a b
    refine Nat.le_of_testBit fun i hi => ?_
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  have hland : (callerArg0 I).toNat
      = Nat.land (callerArg0 I).toNat addrMask.toNat % EVM.twoPow 256 := by
    conv_lhs => rw [heq]
    rfl
  have hmod : Nat.land (callerArg0 I).toNat addrMask.toNat % EVM.twoPow 256
      = Nat.land (callerArg0 I).toNat addrMask.toNat :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (hlandle _ _) (by decide))
  have hmask : addrMask.toNat < EVM.addressModulus := by decide
  rw [hland, hmod]; exact lt_of_le_of_lt (hlandle _ _) hmask

/-! ## Storage coupling: the Solm `.assign stored := v` writes the same word the EVM `SSTORE` does -/

/-- `wordOfInt (Int.ofNat k) = ofNat k` (a nonnegative literal round-trips through `ℤ`). -/
theorem wordOfInt_ofNat_eq (k : ℕ) : EVM.wordOfInt (Int.ofNat k) = UInt256.ofNat k := by
  rw [EVM.wordOfInt, if_neg (by simp)]; apply u256_inj
  show (Int.ofNat k).toNat % EVM.twoPow 256 = (UInt256.ofNat k).toNat
  rw [show (Int.ofNat k).toNat = k from rfl, show (UInt256.ofNat k).toNat = k % UInt256.size from rfl,
      show EVM.twoPow 256 = UInt256.size from by decide]

/-- The little-endian byte serialization round-trips: `fromBytes' (toBytesLE w) = w.toNat`. -/
theorem fromBytesLE_roundtrip (w : UInt256) :
    fromBytes' (EVM.Word.toBytesLEWithSizeProof w).1 = w.toNat := by
  show fromBytes' (toBytes' w.val ++ List.replicate (32 - (toBytes' w.val).length) 0) = w.toNat
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']; rfl

/-- **Whole-slot store.**  Storing `.int k` into the `stored` location (slot 0, offset 0, size 32)
    writes exactly the word `ofNat k` — i.e. the value the EVM `SSTORE`s. -/
theorem callerLocStore (evm' : EVM.State) (k : ℕ) :
    storageLocStore evm'
        { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide,
          bitOffset := .none,
          type := .int (.uint ⟨256, by decide⟩) } (.int (Int.ofNat k))
      = some (EVM.storageStore evm' evm'.executionEnv.codeOwner ⟨0⟩ (UInt256.ofNat k)) := by
  unfold storageLocStore
  simp only [valueToWord, wordOfInt_ofNat_eq, bind, Option.bind, pure, storageLocWriteWord]
  have hslen := (EVM.Word.toBytesLEWithSizeProof (EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat k)).2
  congr 2; apply u256_inj
  show fromBytes' (List.take (0:Fin 32).val _ ++ List.take (32:Fin 33).val _
        ++ List.drop ((0:Fin 32).val + (32:Fin 33).val) _) = (UInt256.ofNat k).toNat
  rw [show (0:Fin 32).val = 0 from rfl, show (32:Fin 33).val = 32 from rfl,
      List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by omega), List.append_nil,
      List.take_of_length_le (by omega), fromBytesLE_roundtrip]

/-- **The Solm `.assign stored := .int k` step.**  Dispatches to the storage write (the local
    `stored` is absent, `hbase`), producing the post-`SSTORE` EVM state. -/
theorem callerAssign (evm' : EVM.State) (L : Solm.Store) (k : ℕ) (hbase : L.get? "stored" = none) :
    assignStorageRef? callerConfig { contract := callerContract, locals := L } evm'
        .storage { base := "stored", steps := [] } (.int (Int.ofNat k))
      = .ok ({ contract := callerContract, locals := L },
             EVM.storageStore evm' evm'.executionEnv.codeOwner ⟨0⟩ (UInt256.ofNat k)) := by
  have her : evalStorageRef callerConfig { contract := callerContract, locals := L } evm'
      { base := "stored", steps := [] } = .ok { base := "stored", steps := [] } := by
    simp [evalStorageRef, bind, EvalResult.bind, pure]
  have hty : storageTypeAt? callerContract.storage { base := "stored", steps := [] } =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := by
    simp [storageTypeAt?, callerContract]
  have hloc : callerConfig.storage.layout { base := "stored", steps := [] } =
      fun _ => some { slot := ⟨0⟩, offset := 0, size := 32, hbound := (by decide),
                      bitOffset := .none, type := .int (.uint ⟨256, (by decide)⟩) } := rfl
  exact assignStorageRef_storage_scalar hbase her hty hloc (callerLocStore evm' k)

theorem land_mask160 (n : ℕ) (h : n < 2^160) : Nat.land n (2^160 - 1) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  show (n &&& (2^160-1)).testBit i = n.testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 160
  · rw [decide_eq_true hi, Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false]
    have : n < 2^i := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact (Nat.testBit_lt_two_pow this).symm

theorem callerCanon_eq {I : ExecutionEnv} (hcanon : (callerArg0 I).toNat < EVM.addressModulus) :
    UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩ := by
  have hland : UInt256.land (callerArg0 I) addrMask = callerArg0 I := by
    apply u256_inj
    show Nat.land (callerArg0 I).toNat addrMask.toNat % EVM.twoPow 256 = (callerArg0 I).toNat
    rw [show addrMask.toNat = 2 ^ 160 - 1 from by decide,
        land_mask160 _ (by rw [show EVM.addressModulus = 2^160 from by decide] at hcanon; exact hcanon)]
    exact Nat.mod_eq_of_lt (by have := (callerArg0 I).val.isLt; simpa [UInt256.size, EVM.twoPow, UInt256.toNat] using this)
  rw [hland]; exact ueq_self (callerArg0 I)

/-! ## Decode-failure EVM revert traces (datalen / signed / clean-address checks) -/

theorem callerX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz hshort hsize
  obtain ⟨k0, C0, rd0⟩ := callerX_toDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  have rd := evm_run rd0 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push2 ⟨370⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨369⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]
  exact rd

theorem callerX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨k0, C0, rd0⟩ := callerX_toDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  have rd := evm_run rd0 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push2 ⟨370⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨369⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]
  exact rd

theorem ueq_zero_of_ne {a b : UInt256} (h : ¬ UInt256.eq a b = ⟨1⟩) : UInt256.eq a b = ⟨0⟩ := by
  by_cases hab : a = b
  · subst hab; exact absurd (ueq_self a) h
  · show UInt256.fromBool (decide (a = b)) = ⟨0⟩
    rw [decide_eq_false hab]; rfl

theorem callerX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hnc : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨0⟩) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := callerX_dec264 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact (evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨274⟩, jumpiNT (by rw [hnc]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I))

/-! ## Decoded-store accessors and the canonical-execution coupling -/

theorem store_get_empty (k : Ident) : (∅ : Solm.Store).get? k = none := by simp
abbrev callerDecStore (I : ExecutionEnv) : Solm.Store :=
  ((∅:Solm.Store).insert "t" (.address (AccountAddress.ofNat (callerArg0 I).toNat))).insert "n"
    (.int (Int.ofNat (callerArg1 I).toNat))
theorem callerStore_t (I : ExecutionEnv) :
    (callerDecStore I).get? "t" = some (.address (AccountAddress.ofNat (callerArg0 I).toNat)) := by
  rw [callerDecStore, store_get_ne _ _ (by decide), store_get_self]
theorem callerStore_n (I : ExecutionEnv) :
    (callerDecStore I).get? "n" = some (.int (Int.ofNat (callerArg1 I).toNat)) := by
  rw [callerDecStore, store_get_self]
theorem callerStore_stored (I : ExecutionEnv) (v : Value) :
    ((callerDecStore I).insert "tmp" v).get? "stored" = none := by
  rw [store_get_ne _ _ (by decide), callerDecStore, store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_empty]
theorem ofNat_toNat_lt (n : ℕ) (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
  ulit_toNat' n h
theorem callerL_succ (n : ℕ) (h1 : 32 ≤ n) (h2 : n < UInt256.size) :
    (min (⟨32⟩:UInt256) (UInt256.ofNat n)).toNat = 32 := by
  show (if (⟨32⟩:UInt256) ≤ UInt256.ofNat n then (⟨32⟩:UInt256) else UInt256.ofNat n).toNat = 32
  rw [if_pos (show (⟨32⟩:UInt256) ≤ UInt256.ofNat n from ?_)]
  · rfl
  · show (32:ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl, ofNat_toNat_lt n h2]; omega
theorem callerL_rev (n : ℕ) (h : n < 32) :
    (min (⟨32⟩:UInt256) (UInt256.ofNat n)).toNat = n := by
  show (if (⟨32⟩:UInt256) ≤ UInt256.ofNat n then (⟨32⟩:UInt256) else UInt256.ofNat n).toNat = n
  have hnsize : n < UInt256.size := by
    have h32 : 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  rw [if_neg (show ¬ (⟨32⟩:UInt256) ≤ UInt256.ofNat n from ?_), ofNat_toNat_lt n hnsize]
  · show ¬ (32:ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ofNat_toNat_lt n hnsize]; omega
theorem write_len_zero (src base : ByteArray) (sa da : ℕ) : src.write sa base da 0 = base := by
  rw [ByteArray.write]; rfl
theorem callerWrite_size (I : ExecutionEnv) (o : ByteArray) (L : ℕ) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (callerCalldataMem I) 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h; rw [write_len_zero]; exact callerCalldataMem_size I
  · rw [write_eq_gen o (callerCalldataMem I) 128 L (by omega) hLo (by rw [callerCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, callerCalldataMem_size]; omega
theorem callerWrite_read64 (I : ExecutionEnv) (o : ByteArray) (L : ℕ) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (callerCalldataMem I) 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h; rw [write_len_zero]; exact callerCalldataMem_read64 I
  · rw [write_read_below_gen o (callerCalldataMem I) 128 L 64 (by omega) hLo
      (by rw [callerCalldataMem_size]; omega) (by omega), callerCalldataMem_read64]

-- The state-changing return bridges (`RDret.reEquivExecutionGenAccountMapEquiv`,
-- `RDret.reEquivExecutionGenEVMStateEquiv`) live next to `RDret.reEquivExecution` in
-- `Reasoning/Dispatch.lean`.

set_option maxHeartbeats 1000000 in
theorem callerExec_canonical {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor callerConfig callerContract cA gh bl
      σ_evm σ_solm σ₀ g.toUInt256 A I := by
  have hcanon := callerArg0_canonical hclean
  have hd : dispatchMsg callerContract I.calldata = some runTransition := by
    rw [callerDispatch.eq, if_pos hmatch]
  have hdec := callerDecode_n hsz68 hbig hcanon
  obtain ⟨cA', σ', z, o, A', k', C', rd144, hcoin, hosize⟩ :=
    callerX_postCall (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv (by omega) hsize hsz68 hbig hmatch hclean
      hperm hdepth
  obtain ⟨σ'_solm, A'_solm, hcoin_solm, hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv hcoin (by simp [initState]) hAccounts
  cases z
  · -- z = false: external call failed ⇒ revert
    simp only [Bool.false_eq_true, if_false] at rd144 hcoin hcoin_solm
    refine (callerX_postRevert rd144 (by simp)).reEquivExecutionRevert hcode hd hdec ?_
    exact callerBodyExtFail _ (callerDecStore I) (by exact hwv) (callerStore_t I)
      (callerStore_n I) hcoin_solm
  · -- z = true
    simp only [if_true] at rd144 hcoin hcoin_solm
    by_cases ho255 : o.size < 2 ^ 255
    · by_cases ho32 : 32 ≤ o.size
      · -- success: `32 ≤ |o| < 2^255`
        rw [callerOutPtr_eq, show (⟨128⟩:UInt256).toNat = 128 from by decide,
            callerL_succ o.size ho32 hosize] at rd144
        have hmsz : 160 ≤ (o.write 0 (callerCalldataMem I) 128 32).size := by
          have := callerWrite_size I o 32 (by omega) ho32; omega
        have hfp : (if (⟨64⟩:UInt256).toNat ≥ (o.write 0 (callerCalldataMem I) 128 32).size
                ∨ (⟨64⟩:UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
              else UInt256.ofNat (fromByteArrayBigEndian
                ((o.write 0 (callerCalldataMem I) 128 32).readWithPadding (⟨64⟩:UInt256).toNat 32))) = ⟨128⟩ := by
          exact mloadFreePtrValue (by rw [callerWrite_size I o 32 (by omega) ho32]; decide)
            (by decide) (callerWrite_read64 I o 32 (by omega) ho32)
        have hword : (o.write 0 (callerCalldataMem I) 128 32).readWithPadding 128 32 = o.extract 0 32 :=
          write32_read_back o (callerCalldataMem I) 128 ho32 (by rw [callerCalldataMem_size]; omega)
        have hrd := callerX_successChain rd144 hperm ho32 ho255 hfp hword hmsz
        -- Solm body
        set evmP : EVM.State := { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' } with hevmP
        set kw := fromByteArrayBigEndian (o.extract 0 32) with hkw
        have hassign := callerAssign evmP ((callerDecStore I).insert "tmp" (.int (Int.ofNat kw))) kw
          (callerStore_stored I _)
        have hdecv : callerConfig.externalABI.decode? "pow2" o = some (.int (Int.ofNat kw)) := by
          show defaultDecodeReturn? "pow2" o = _
          simpa [defaultDecodeReturn?, ← hkw, Int.ofNat_eq_natCast] using
            decodeReturnValue_uint256_ok (returndata := o) ho32 ho255
        have hbody := callerBodySuccess (initState cA gh bl σ_solm σ₀ g A I)
          (callerDecStore I) (by exact hwv) (callerStore_t I) (callerStore_n I)
          hcoin_solm hdecv hassign
        exact RDret.reEquivExecutionGenEVMStateEquiv hcode hrd hd hdec hbody
          (by rw [storageStore_createdAccounts])
          (accountMapEquiv.of_eq (by rw [storageStore_accountMap]; simp [initState]))
          (hStateCall.storageStore_codeOwner ⟨0⟩ rfl)
          (returnEquiv.void rfl rfl rfl)
      · -- `|o| < 32`: decode reverts
        rw [not_le] at ho32
        rw [callerOutPtr_eq, show (⟨128⟩:UInt256).toNat = 128 from by decide,
            callerL_rev o.size ho32] at rd144
        have hfp2 : (if (⟨64⟩:UInt256).toNat ≥ (o.write 0 (callerCalldataMem I) 128 o.size).size
                ∨ (⟨64⟩:UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
              else UInt256.ofNat (fromByteArrayBigEndian
                ((o.write 0 (callerCalldataMem I) 128 o.size).readWithPadding (⟨64⟩:UInt256).toNat 32))) = ⟨128⟩ := by
          exact mloadFreePtrValue
            (by rw [callerWrite_size I o o.size (by omega) (by omega)]; decide)
            (by decide) (callerWrite_read64 I o o.size (by omega) (by omega))
        obtain ⟨k1, C1, rd165⟩ := callerX_succ_to165 rd144 (by simp)
        obtain ⟨k2, C2, rd470⟩ := callerX_succ_to470 rd165 hfp2
        refine (callerX_succ_revert rd470 ho32).reEquivExecutionRevert hcode hd hdec ?_
        have hdecn : callerConfig.externalABI.decode? "pow2" o = none := by
          show defaultDecodeReturn? "pow2" o = none
          simpa [defaultDecodeReturn?] using
            decodeReturnValue_uint256_none_short (returndata := o) ho32
        exact callerBodyDecodeRevert _ (callerDecStore I) (by exact hwv) (callerStore_t I)
          (callerStore_n I) hcoin_solm hdecn
    · -- `2^255 ≤ |o| < 2^256`: the ABI decoder and solc signed check both revert.
      have hhi : 2 ^ 255 ≤ o.size := by omega
      have ho32 : 32 ≤ o.size := by omega
      rw [callerOutPtr_eq, show (⟨128⟩:UInt256).toNat = 128 from by decide,
          callerL_succ o.size ho32 hosize] at rd144
      have hfp : (if (⟨64⟩:UInt256).toNat ≥ (o.write 0 (callerCalldataMem I) 128 32).size
              ∨ (⟨64⟩:UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
            else UInt256.ofNat (fromByteArrayBigEndian
              ((o.write 0 (callerCalldataMem I) 128 32).readWithPadding (⟨64⟩:UInt256).toNat 32))) = ⟨128⟩ := by
        exact mloadFreePtrValue (by rw [callerWrite_size I o 32 (by omega) ho32]; decide)
          (by decide) (callerWrite_read64 I o 32 (by omega) ho32)
      obtain ⟨k1, C1, rd165⟩ := callerX_succ_to165 rd144 (by simp)
      obtain ⟨k2, C2, rd470⟩ := callerX_succ_to470 rd165 hfp
      refine (callerX_succ_revert_huge rd470 hhi hosize).reEquivExecutionRevert hcode hd hdec ?_
      have hdecn : callerConfig.externalABI.decode? "pow2" o = none := by
        show defaultDecodeReturn? "pow2" o = none
        simpa [defaultDecodeReturn?] using
          decodeReturnValue_uint256_none_huge (returndata := o) hhi
      exact callerBodyDecodeRevert _ (callerDecStore I) (by exact hwv) (callerStore_t I)
        (callerStore_n I) hcoin_solm hdecn

theorem callerX_callDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩)
    (hdepth : I.depth = 1024) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd142⟩ := callerX_toCall142 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  obtain ⟨gv, rd143⟩ := rd142.gas (by decide) (by evm_ov)
  obtain ⟨k', C', rd144⟩ := rd143.callDepthLimit (by decide) hdepth (by evm_ov)
  exact callerX_postRevert rd144 (by simp)

/-! ## The `callvalue = 0` Solm coupling -/

theorem callerReEquiv_callvalueZero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor callerConfig callerContract cA gh bl
      σ_evm σ_solm σ₀ g.toUInt256 A I := by
  by_cases hsz : I.calldata.size < 4
  · exact (callerX_cvz_short hcode hwv hsz).reEquivNoDispatch hcode (callerDispatch.none_short hsz)
  · rw [not_lt] at hsz
    by_cases hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · -- matching selector → dispatch succeeds
      have hd : dispatchMsg callerContract I.calldata = some runTransition := by
        rw [callerDispatch.eq, if_pos hmatch]
      by_cases hsz68 : 68 ≤ I.calldata.size
      · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
        · by_cases hcanon : (callerArg0 I).toNat < EVM.addressModulus
          · -- valid decode: the external call executes; its outcome depends only on the depth limit
            by_cases hdepth : I.depth.val < 1024
            · exact callerExec_canonical hcode hwv hsize hperm hdepth hsz68 hbig hmatch
                (callerCanon_eq hcanon) hAccounts
            · -- call-depth limit reached ⇒ the `CALL` returns 0 immediately (both sides revert)
              rw [not_lt] at hdepth
              have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
              refine (callerX_callDepthLimit hcode hwv (by omega) hsize hsz68 hbig hmatch
                  (callerCanon_eq hcanon) hdepth1024).reEquivExecutionRevert hcode hd
                (callerDecode_n hsz68 hbig hcanon) ?_
              exact callerBodyExtFail _ (callerDecStore I) (by exact hwv) (callerStore_t I)
                (callerStore_n I) (callNotMade_depthLimit (callerEncode_eq I) hdepth1024)
          · exact (callerX_noncanon hcode hwv (by omega) hsize hsz68 hbig hmatch
                (ueq_zero_of_ne (fun he => hcanon (callerArg0_canonical he)))).reEquivDecodingFailed
              hcode hd (callerDecode_none_noncanon hsz68 hbig hcanon)
        · rw [not_lt] at hbig
          exact (callerX_hugearg hcode hwv (by omega) hsize hbig hmatch).reEquivDecodingFailed
            hcode hd (callerDecode_none_huge hbig)
      · rw [not_le] at hsz68
        exact (callerX_shortarg hcode hwv hsz hsize hsz68 hmatch).reEquivDecodingFailed
          hcode hd (callerDecode_none_short hsz hsz68)
    · rw [Bool.not_eq_true] at hmatch
      exact (callerX_cvz_revertB hcode hwv hsz hsize hmatch).reEquivNoDispatch hcode
        (callerDispatch.none_nomatch hmatch)

/-! ## The correctness statement -/

/-- The runtime bytecode refines the Solm specification, for every initial state. -/
theorem callerCorrect :
    runtimeEquivalence!?! callerConfig callerBytecode callerContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I
      hcode hsize hperm hσ => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact callerReEquiv_callvalueZero (g := Sat256.ofUInt256 g) hcode hsize hwv hperm hσ
  · exact (callerX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivNonPayable hcode rfl
      fun _ca => bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end Caller
