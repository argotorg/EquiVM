import Solm.Semantics
import Reasoning.Reach
import Reasoning.Storage

/-!
# Dispatch — generic Solm `dispatchMsg` facts

`dispatchMsg` (the trusted Solm dispatcher) maps each transition to its 4-byte keccak selector and
returns the first whose selector matches the calldata prefix.  Everything here is contract-agnostic:

- **Multi-selector dispatch**: `dispatchList`, the pure list-recursive form of `dispatchMsg`, plus
  the bridge and list-walking lemmas that handle a contract with any number of functions;
- **Single-transition instances** (`contract.transitions = [transition]`): `dispatchMsg` reduces
  to a 4-byte calldata-prefix compare, instantiated per contract with its `transitions = [t]`
  proof (`rfl`) and its selector axiom, bundled in `SingleSelectorDispatch`;
- **`Reasoning.Reach` bridges** (`RDret`/`RDrev.reEquiv*`): package the runtime-equivalence
  coupling, e.g. `RDrev.reEquivNonPayable` for the whole `callvalue ≠ 0` branch.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Reasoning.Theory

variable {contract : ContractDecl} {transition : TransitionDecl} {selBytes : ByteArray}

/-! ## Generic multi-selector dispatch

`dispatchMsg` (the trusted Solm dispatcher) maps each transition to its 4-byte keccak selector and
returns the first whose selector matches the calldata prefix.  `dispatchList` is its pure
list-recursive form and `dispatchMsg_eq_dispatchList` bridges the two, after which a contract with
*any* number of functions is handled by walking the list with `dispatchList_cons` / `dispatchList_nil`
and the per-transition selector axioms.  The single-transition lemmas below are the `n = 1`
instances. -/

/-- The 4-byte function selector of a transition, `keccak(signature)[0:4]`. -/
def selectorOf (t : TransitionDecl) : ByteArray :=
  (ffi.KEC (String.toByteArray (transitionSigStr t))).extract 0 4

/-- Pure list form of `dispatchMsg`: the first transition whose selector matches `cd`'s 4-byte
    prefix, scanning in order. -/
def dispatchList : List TransitionDecl → ByteArray → Option TransitionDecl
  | [],      _  => none
  | t :: ts, cd => if selectorOf t == cd.extract 0 4 then some t else dispatchList ts cd

@[simp] theorem dispatchList_nil (cd : ByteArray) : dispatchList [] cd = none := rfl

theorem dispatchList_cons (t : TransitionDecl) (ts : List TransitionDecl) (cd : ByteArray) :
    dispatchList (t :: ts) cd =
      if selectorOf t == cd.extract 0 4 then some t else dispatchList ts cd := rfl

/-- `selectorDispatchMsg` agrees with its pure list form. -/
theorem selectorDispatchMsg_eq_dispatchList (contract : ContractDecl) (cd : ByteArray) :
    selectorDispatchMsg contract cd = dispatchList contract.transitions cd := by
  simp only [selectorDispatchMsg]
  generalize contract.transitions = ts
  induction ts with
  | nil => simp [dispatchList]
  | cons t ts ih =>
    simp only [List.map_cons, List.find?_cons, Prod.map, id_eq, Function.comp_apply]
    rw [dispatchList_cons, selectorOf]
    by_cases hb : ((ffi.KEC (String.toByteArray (transitionSigStr t))).extract 0 4
        == cd.extract 0 4) = true
    · rw [if_pos hb]; simp only [hb]
    · rw [if_neg hb]; simp only [Bool.not_eq_true] at hb; simp only [hb]; exact ih

/-- `dispatchMsg` agrees with its pure list form for contracts with no receive/fallback — the bridge
    that lets the single-selector lemmas (and any example's N-way dispatch) reason about
    `dispatchList`. -/
theorem dispatchMsg_eq_dispatchList (contract : ContractDecl) (cd : ByteArray)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd = dispatchList contract.transitions cd := by
  rw [dispatchMsg, selectorDispatchMsg_eq_dispatchList contract cd]
  cases dispatchList contract.transitions cd <;> simp [receiveDispatchMsg, hreceive, hfallback]

/-- Calldata shorter than a selector dispatches to nothing, for **any** number of transitions
    (every selector is 4 bytes, so none can equal a `< 4`-byte prefix). -/
theorem dispatchList_none_short (ts : List TransitionDecl)
    (hsz : ∀ t ∈ ts, (selectorOf t).size = 4) {cd : ByteArray} (hcd : cd.size < 4) :
    dispatchList ts cd = none := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [dispatchList_cons]
    have hfalse : (selectorOf t == cd.extract 0 4) = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have heq := byteArray_size_eq_of_beq hc
      rw [ByteArray.size_extract, hsz t (by simp)] at heq
      omega
    rw [if_neg (by rw [hfalse]; simp)]
    exact ih (fun t' ht' => hsz t' (List.mem_cons_of_mem _ ht'))

/-- A successful equality check against a 4-byte selector prefix implies calldata has at least
    four bytes. -/
theorem calldata_size_ge_of_selIs (I : ExecutionEnv) (sel : ByteArray) (hselSize : sel.size = 4)
    (hsel : (sel == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [hselSize, ByteArray.size_extract] at hs
  omega

/-- A transition returned by `dispatchList` is a member of the scanned list. -/
theorem dispatchList_some_mem {ts : List TransitionDecl} {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchList ts cd = some t) : t ∈ ts := by
  induction ts with
  | nil => simp [dispatchList] at h
  | cons head tail ih =>
      rw [dispatchList_cons] at h
      by_cases hb : (selectorOf head == cd.extract 0 4) = true
      · rw [if_pos hb] at h; cases h; simp
      · rw [if_neg hb] at h; exact List.mem_cons_of_mem head (ih h)

/-- If **no** transition's selector matches the calldata prefix, dispatch yields nothing — the
    n-ary form of `dispatch_none_nomatch`. -/
theorem dispatchList_none_of_all_ne {ts : List TransitionDecl} {cd : ByteArray}
    (h : ∀ t ∈ ts, (selectorOf t == cd.extract 0 4) = false) :
    dispatchList ts cd = none := by
  induction ts with
  | nil => rfl
  | cons head tail ih =>
      rw [dispatchList_cons, if_neg (by rw [h head (by simp)]; simp)]
      exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- **First-match dispatch** (n-ary positive form): every transition before `ti` misses the
    calldata prefix and `ti` hits it, so dispatch returns `ti`.  Subsumes the `dispatch_eq`/`if_pos`
    positive case (`pre = []`) and the per-arm `dispatchList_cons` folds. -/
theorem dispatchList_eq_some_of_split {pre post : List TransitionDecl} {ti : TransitionDecl}
    {cd : ByteArray}
    (hpre : ∀ t ∈ pre, (selectorOf t == cd.extract 0 4) = false)
    (hhit : (selectorOf ti == cd.extract 0 4) = true) :
    dispatchList (pre ++ ti :: post) cd = some ti := by
  induction pre with
  | nil => rw [List.nil_append, dispatchList_cons, if_pos hhit]
  | cons head tail ih =>
      rw [List.cons_append, dispatchList_cons, if_neg (by rw [hpre head (by simp)]; simp)]
      exact ih (fun t ht => hpre t (List.mem_cons_of_mem _ ht))

/-- `dispatchMsg` no-match, n-ary: no transition selector matches ⇒ no dispatch. -/
theorem dispatchMsg_none_of_all_ne {contract : ContractDecl} {cd : ByteArray}
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl)
    (h : ∀ t ∈ contract.transitions, (selectorOf t == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd hfallback hreceive]
  exact dispatchList_none_of_all_ne h

/-- `dispatchMsg` first-match, n-ary: the transitions split as `pre ++ ti :: post`, every `pre`
    selector misses and `ti`'s hits ⇒ dispatch returns `ti`. -/
theorem dispatchMsg_eq_some_of_split {contract : ContractDecl} {pre post : List TransitionDecl}
    {ti : TransitionDecl} {cd : ByteArray}
    (hfallback : contract.fallback = none := by rfl)
    (htr : contract.transitions = pre ++ ti :: post)
    (hpre : ∀ t ∈ pre, (selectorOf t == cd.extract 0 4) = false)
    (hhit : (selectorOf ti == cd.extract 0 4) = true)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd = some ti := by
  rw [dispatchMsg_eq_dispatchList contract cd hfallback hreceive, htr]
  exact dispatchList_eq_some_of_split hpre hhit

/-- `dispatchMsg` of a single-transition contract is the selector compare — the `n = 1` instance of
    the `dispatchList` framework above. -/
theorem dispatch_eq
    (hfallback : contract.fallback = none := by rfl)
    (htr : contract.transitions = [transition])
    (hsel : (ffi.KEC (String.toByteArray (Solm.transitionSigStr transition))).extract 0 4 = selBytes)
    (cd : ByteArray)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd = if (selBytes == cd.extract 0 4) then some transition else none := by
  rw [dispatchMsg_eq_dispatchList contract cd hfallback hreceive, htr, dispatchList_cons,
    dispatchList_nil, selectorOf, hsel]

/-- A single-transition contract dispatches only to that transition. -/
theorem dispatch_unique
    (hfallback : contract.fallback = none := by rfl)
    (htr : contract.transitions = [transition])
    {cd : ByteArray} {t : TransitionDecl} (h : dispatchMsg contract cd = some t)
    (hreceive : contract.receive = none := by rfl) :
    t = transition := by
  have hsel := selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some hreceive hfallback h
  rw [selectorDispatchMsg_eq_dispatchList contract cd, htr, dispatchList_cons, dispatchList_nil]
    at hsel
  by_cases hb : (selectorOf transition == cd.extract 0 4) = true
  · rw [if_pos hb] at hsel
    cases hsel
    rfl
  · rw [if_neg hb] at hsel
    simp at hsel

/-- Calldata shorter than the 4-byte selector cannot dispatch. -/
theorem dispatch_none_short
    (hfallback : contract.fallback = none := by rfl)
    (htr : contract.transitions = [transition])
    (hsel : (ffi.KEC (String.toByteArray (Solm.transitionSigStr transition))).extract 0 4 = selBytes)
    (hsize : selBytes.size = 4) {cd : ByteArray} (h : cd.size < 4)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd = none := by
  rw [dispatch_eq hfallback htr hsel _ hreceive]
  have hfalse : (selBytes == cd.extract 0 4) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hsz := byteArray_size_eq_of_beq hc
    rw [ByteArray.size_extract] at hsz
    simp only [hsize] at hsz
    omega
  simp [hfalse]

/-- A selector mismatch cannot dispatch. -/
theorem dispatch_none_nomatch
    (hfallback : contract.fallback = none := by rfl)
    (htr : contract.transitions = [transition])
    (hsel : (ffi.KEC (String.toByteArray (Solm.transitionSigStr transition))).extract 0 4 = selBytes)
    {cd : ByteArray} (h : (selBytes == cd.extract 0 4) = false)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd = none := by
  rw [dispatch_eq hfallback htr hsel _ hreceive]; simp [h]

/-! ## Single-selector bundle

The three single-transition facts (`dispatch_eq` / `dispatch_none_short` / `dispatch_none_nomatch`)
packaged into one record.  A single-function example builds it once from its `transitions = [t]`
proof and selector axiom (`singleSelectorDispatch`), then uses `.eq` / `.none_short` / `.none_nomatch`
in place of the hand-written per-contract dispatch triple. -/

/-- Bundle of the three single-selector dispatch facts for a one-transition contract. -/
structure SingleSelectorDispatch (contract : ContractDecl) (transition : TransitionDecl)
    (selBytes : ByteArray) : Prop where
  eq : ∀ cd : ByteArray, dispatchMsg contract cd
        = if (selBytes == cd.extract 0 4) then some transition else none
  none_short : ∀ {cd : ByteArray}, cd.size < 4 → dispatchMsg contract cd = none
  none_nomatch : ∀ {cd : ByteArray}, (selBytes == cd.extract 0 4) = false →
        dispatchMsg contract cd = none

/-- Build the single-selector bundle from a single-transition contract proof (`htr`), its selector
    axiom (`hsel`, the usual `keccak(sig)[0:4] = selBytes`), and `selBytes.size = 4`. -/
theorem singleSelectorDispatch
    (hfallback : contract.fallback = none := by rfl)
    (htr : contract.transitions = [transition])
    (hsel : (ffi.KEC (String.toByteArray (Solm.transitionSigStr transition))).extract 0 4 = selBytes)
    (hsize : selBytes.size = 4)
    (hreceive : contract.receive = none := by rfl) :
    SingleSelectorDispatch contract transition selBytes where
  eq cd := dispatch_eq hfallback htr hsel cd hreceive
  none_short h := dispatch_none_short hfallback htr hsel hsize h hreceive
  none_nomatch h := dispatch_none_nomatch hfallback htr hsel h hreceive

/-- The EVM return bytes `o` couple to the Solm return value `rv` whenever `o` is `rv`'s ABI
    encoding (the `returned` case of `returnEquiv`). -/
theorem returnEquiv_of_encode {abit : ABIType} {rv : Value} {o : ByteArray}
    (h : encodeReturnValue? abit rv = some o) :
    returnEquiv o (some [rv]) [abit] :=
  returnEquiv.returned rfl h

end Reasoning.Theory

namespace Reasoning.Reach

/-- **The whole `callvalue ≠ 0` Solm coupling**, generic over a single-transition contract.  Given the
    non-payable guard's revert (`h : RDrev …`) and the contract body's revert under non-zero call
    value (`hbody`), produce the `runtimeEquivalenceFor` case: the OOG alternative folds via
    `reEquivElim`, and the Solm side is dispatched abstractly into `noDispatch` / `decodingFailed` /
    `execution`-with-revert.  Each example's `callvalue ≠ 0` branch is a single call to this. -/
theorem RDrev.reEquivNonPayable {cfg : Config} {contract : ContractDecl} {transition : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (hfallback : contract.fallback = none := by rfl)
    (htr : contract.transitions = [transition])
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hbody : ∀ callargs, ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I)
              callargs transition.body .reverted)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => by
    by_cases hdisp : dispatchMsg contract I.calldata = none
    · exact reEquiv_noDispatch hdisp hrev
    · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
      cases Reasoning.Theory.dispatch_unique hfallback htr ht hreceive
      by_cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
          (transitionSignature transition).paramTypes I.calldata = none
      · exact reEquiv_decodingFailed ht hdec hrev hfallback hreceive
      · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
        exact reEquiv_execution ht hca (hbody callargs) (by rw [hrev]; exact .revert rfl rfl)
          hfallback hreceive

/-- `RDret ⇒ execution` (success), state-changing form with account maps compared up to
    observable account/storage reads.  This is useful when bytecode coalesces packed storage writes
    that Solm performs as multiple same-slot updates, which can leave `RBMap`s with different
    internal shapes but identical account presence, account metadata, and storage lookups. -/
theorem RDret.reEquivExecutionGenAccountMapEquiv {cfg : Config} {contract : ContractDecl}
    {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code o : ByteArray} {callargs cs retVal}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {evm'' : EVM.State}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) acc o)
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs evm'' retVal))
    (hCreated : acc.1 = evm''.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evm''.accountMap)
    (henc : returnEquiv o retVal t.returnType)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hsacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body (.returned cs evm'' retVal) := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine reEquiv_execution hd hdec hbody' ?_ hfallback hreceive
    rw [hxi]
    have hcreated : s.createdAccounts = evm''.createdAccounts := by
      exact (congrArg Prod.fst hsacc).trans hCreated
    have haccounts : accountMapEquiv s.accountMap evm''.accountMap := by
      change accountMapEquiv (s.createdAccounts, s.accountMap).2 evm''.accountMap
      rw [congrArg Prod.snd hsacc]
      exact hAccounts
    exact execResultsEquiv.success rfl rfl hcreated haccounts (.abi henc)

/-- `RDret ⇒ execution` (success), **`EVMStateEquiv` simulation form**: the EVM-side post-state
    `evm'_evm` and the Solm body's post-state `evm'_solm` are related by the simulation relation
    `EVMStateEquiv` (built compositionally from `EVMStateEquiv.initState`/`.storageStore*`), and the
    run's returned `acc` matches `evm'_evm` up to the same observational account equality used
    elsewhere — `acc.1` equal on created accounts, `acc.2` equal *up to `accountMapEquiv`*.  The
    up-to form on `acc.2` (rather than strict equality) lets this apply when the bytecode result and
    the Solm spec coalesce to different `RBMap` shapes (e.g. packed same-slot double writes). -/
theorem RDret.reEquivExecutionGenEVMStateEquiv {cfg : Config} {contract : ContractDecl}
    {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code o : ByteArray} {callargs cs retVal}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evm'_evm evm'_solm : EVM.State}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) acc o)
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs evm'_solm retVal))
    (hCreated : acc.1 = evm'_evm.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evm'_evm.accountMap)
    (hState : EVMStateEquiv evm'_evm evm'_solm)
    (henc : returnEquiv o retVal t.returnType)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (hCreated.trans hState.createdAccounts)
    (accountMapEquiv.trans hAccounts hState.accountMap)
    henc hfallback hreceive

/-- `RDret ⇒ execution` (success): the run returns bytes `o`, the dispatched Solm body returns
    `retVal` leaving the EVM state at `initState`, and `o` is `retVal`'s ABI encoding (`henc`).
    The non-mutating special case of `reEquivExecutionGenAccountMapEquiv` (`evm'' = initState …`). -/
theorem RDret.reEquivExecution {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code o : ByteArray} {callargs cs retVal}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs (initState cA gh bl σ_solm σ₀ g A I) retVal))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (henc : returnEquiv o retVal t.returnType)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [initState]) (by simpa [initState] using hAccounts) henc hfallback hreceive

/-- `RDret ⇒ execution` (success), **read-only/getter form**: the Solm body naturally returns the
    value read from `σ_solm` (`rvSolm`), while the EVM output `o` encodes the value read from `σ_evm`
    (`rvEvm`).  The caller supplies the value-level coupling `hval : rvSolm = rvEvm` — typically the
    `accountMapEquiv` read-agreement lifted to the returned value — so the body is passed in its
    natural `σ_solm` form, with no second restatement transported to `σ_evm`. -/
theorem RDret.reEquivExecutionTransport {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code o : ByteArray} {callargs cs rvSolm rvEvm}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
              (.returned cs (initState cA gh bl σ_solm σ₀ g A I) rvSolm))
    (hval : rvSolm = rvEvm)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (henc : returnEquiv o rvEvm t.returnType)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  subst hval
  exact h.reEquivExecution hcode hd hdec hbody hAccounts henc hfallback hreceive

/-- `RDrev ⇒ execution` (revert): the run reverts and the dispatched Solm body reverts too. -/
theorem RDrev.reEquivExecutionRevert {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {code : ByteArray}
    {callargs}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ g A I) callargs t.body .reverted)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => by
    refine reEquiv_execution hd hdec hbody ?_ hfallback hreceive
    rw [hrev]; exact execResultsEquiv.revert rfl rfl

end Reasoning.Reach
