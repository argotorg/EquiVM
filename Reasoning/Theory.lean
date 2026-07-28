import Solm.Equiv
import Ethereum.Theory.ProgressLemmas
import Ethereum.Theory.OpcodeLemmas

/-!
# Theory — reusable, compositional lemmas for runtime-equivalence proofs

General, **contract-agnostic** infrastructure for proving
`runtimeEquivalence cfg bytecode contract`.

Lemmas here are about `runtimeEquivalenceFor`, `actExec`, `execResultsEquiv`,
`returnEquiv`, and the EVM driver `Ethereum.EVM.Ξ` / `X` / `Xstep` — never about a
specific contract. Each example's `Correct.lean` assembles them with its contract-specific facts.

The backbone is a *symbolic-execution* discipline:
* `initState` — the fresh EVM state `Ξ` builds, shared with `actExec`'s `evmState`.
* `Xi_*_of_X` — reduce a fact about `Ξ` to a fact about the fuelled iterator `X`.
* `X_peel` — peel one `Xstep` off `X`, threading the per-instruction gas guard.

Together with the `Ethereum.Theory.OpcodeLemmas` `step_*` lemmas (which evaluate one
`Xstep` to an explicit `if gas < cost then OutOfGass else .ok (next, .none)`), these let
a concrete bytecode trace be run for a *universally quantified* gas `g`.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

/-! ## 1. The initial EVM state -/

/-- The fresh EVM state `Ξ` constructs from the transaction inputs.  Defined to be
    **definitionally** the `freshEvmState` inside `Ethereum.EVM.Ξ` and the `evmState`
    inside `actExec`, so both can be rewritten to mention this single name. -/
def initState
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) : State :=
  { (default : State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }

/-! ## 2. From `Ξ` to the fuelled iterator `X` -/

/-- If the fuelled iterator errors, so does `Ξ`. -/
theorem Xi_error_of_X
    {createdAccounts genesisBlockHeader blocks σ σ₀  A I} {e} {g : UInt256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (.ofUInt256 g) A I) = .error e) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e := by
  unfold Ξ
  simp only [initState, Sat256.ofUInt256] at h
  simp [bind, Except.bind, Sat256.ofUInt256, h]

/-- If the fuelled iterator reverts, so does `Ξ` (same gas/output). -/
theorem Xi_revert_of_X
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g' o} {g : UInt256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (.ofUInt256 g) A I)
          = .ok (.revert g' o)) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .ok (.revert g' o) := by
  unfold Ξ
  simp only [initState, Sat256.ofUInt256] at h
  simp [bind, Except.bind, Sat256.ofUInt256, h]

/-- If the fuelled iterator succeeds (halts), so does `Ξ`, projecting the relevant
    fields of the final machine state. -/
theorem Xi_success_of_X
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {s' o} {g : UInt256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (.ofUInt256 g) A I)
          = .ok (.success s' o)) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = .ok (.success (s'.createdAccounts, s'.accountMap, s'.machineState.gasAvailable.toUInt256,
                       s'.substate) o) := by
  unfold Ξ
  simp only [initState] at h
  simp [bind, Except.bind, h]

/-! ## 2½. `UInt256` gas arithmetic -/

/-- Charging a (small, non-wrapping) gas cost decrements `toNat` by that cost.  The
    side condition `c ≤ g.toNat` rules out the modular wrap. -/
theorem toNat_sub_ofNat {g : Sat256} {c : ℕ} (hc : c ≤ g.toNat) :
    (g.subNat c).toNat = g.toNat - c := by
  have hsize : c < UInt256.size := lt_of_le_of_lt hc g.isLt
  have hofnat : (UInt256.ofNat c).val.val = c := by
    simp [UInt256.ofNat, Id.run, Fin.ofNat, Nat.mod_eq_of_lt hsize]
  have hle : (UInt256.ofNat c).val ≤ g.val := by
    rw [hofnat]; exact hc
  show (g.subNat c).val = g.toNat - c
  rw [← Sat256.toNat, Sat256.subNat_toNat]

/-- A `UInt256` with `toNat = 0` is `⟨0⟩`.  (Used to discharge `callvalue = 0` tests.) -/
theorem uint256_toNat_eq_zero {a : UInt256} (h : a.toNat = 0) : a = ⟨0⟩ := by
  obtain ⟨⟨v, hlt⟩⟩ := a
  simp only [UInt256.toNat] at h
  subst h; rfl

/-! ## 3. Peeling one `Xstep` off `X` -/

/-- **The stepping workhorse.**  Given that one `Xstep` evaluates to the standard
    per-instruction shape `if gas < cost then OutOfGass else .ok (next, .none)` (exactly
    what the `step_*` opcode lemmas produce, once stack-shape/overflow side conditions
    are discharged), peel it off the iterator: `X (f+1)` becomes the same gas guard
    wrapped around `X f` on the successor state.  Holds for *any* fuel `f`. -/
theorem X_peel {vj : Array UInt256} {s s' : State} {P : Prop} [Decidable P] {f : ℕ}
    (h : Xstep vj s = if P then .error .OutOfGass else .ok (s', .none)) :
    X (f + 1) vj s = if P then .error .OutOfGass else X f vj s' := by
  by_cases hg : P
  · simp only [hg, if_true] at h ⊢
    exact Xstep_X_X_except f s vj _ h
  · simp only [hg, if_false] at h ⊢
    exact Xstep_X_X_continue f s s' vj (X f vj s') h rfl

/-- Collapse the two-stage gas guard of a memory opcode (charge `c1` for memory
    expansion, then `c2` for the base cost) into a single guard `gas < c1 + c2`. -/
theorem collapse_two_stage {α : Type _} {gas : Sat256} {c1 c2 : ℕ} {X Y : α} :
    (if gas.toNat < c1 then Y
     else if (gas.subNat c1).toNat < c2 then Y else X)
      = if gas.toNat < c1 + c2 then Y else X := by
  by_cases h1 : gas.toNat < c1
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1]
    by_cases h2 : (gas.subNat c1).toNat < c2
    · rw [if_pos h2, if_pos (by simp [Sat256.toNat, Sat256.subNat] at *; omega)]
    · rw [if_neg h2, if_neg (by simp [Sat256.toNat, Sat256.subNat] at *; omega)]

/-! ## 3½. Trace drivers — peel a step tracking step-count `k` and cumulative cost `C` -/

/-- **Continue a trace** when the current instruction's gas suffices.  Invariants:
    `s` is reached after `k` steps, has gas `g - C` (cumulative cost `C`), and the next
    instruction costs `cost` with `C + cost ≤ g.toNat` (enough gas).  The iterator advances
    one step, decrementing fuel `g.toNat + 1 - k` and growing the cumulative cost. -/
theorem stepContinue {vj : Array UInt256} {s s' : State} {k C cost : ℕ} {g : Sat256}
    (hgas : s.machineState.gasAvailable = g.subNat C)
    (hstep : Xstep vj s
              = if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
                else .ok (s', .none))
    (hk : k ≤ C) (hC : C + cost ≤ g.toNat) :
    X (g.toNat + 1 - k) vj s = X (g.toNat + 1 - (k + 1)) vj s' := by
  have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel, X_peel hstep, hgas]
  have hgg : ¬ (g.toNat - C < cost) := by omega
  simp [hgg]

/-- **Run out of gas** at the current instruction.  Same invariants as `stepContinue`,
    but now the next instruction's `cost` exceeds the remaining gas
    (`g.toNat < C + cost`), so the iterator returns `OutOfGass`. -/
theorem stepOOG {vj : Array UInt256} {s s' : State} {k C cost : ℕ} {g : Sat256}
    (hgas : s.machineState.gasAvailable = g.subNat C)
    (hstep : Xstep vj s
              = if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
                else .ok (s', .none))
    (hk : k ≤ C) (hC : C ≤ g.toNat) (hOOG : g.toNat < C + cost) :
    X (g.toNat + 1 - k) vj s = .error .OutOfGass := by
  have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel, X_peel hstep, hgas]
  have hgg : g.toNat - C < cost := by omega
  simp [hgg]

/-- **Halt** (`RETURN`/`STOP`/`SELFDESTRUCT` ⇒ success, or `REVERT`) when the current
    instruction's gas suffices: the iterator returns the halt result directly. -/
theorem stepHaltSuccess {vj : Array UInt256} {s s' : State} {k C cost : ℕ} {g : Sat256} {o}
    (hgas : s.machineState.gasAvailable = g.subNat C)
    (hstep : Xstep vj s
              = if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
                else .ok (s', .some (.success, o)))
    (hk : k ≤ C) (hC : C + cost ≤ g.toNat) :
    X (g.toNat + 1 - k) vj s = .ok (.success s' o) := by
  have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel]
  have hgg : ¬ (s.machineState.gasAvailable.toNat < cost) := by rw [hgas]; simp [Sat256.subNat, Sat256.toNat] at *; omega
  exact Xstep_X_X_halt_success _ s s' vj o (by rw [hstep]; simp [hgg])

/-- **Halt with revert** when the current instruction's gas suffices: the iterator returns the
    revert result directly. -/
theorem stepHaltRevert {vj : Array UInt256} {s s' : State} {k C cost : ℕ} {g : Sat256} {o}
    (hgas : s.machineState.gasAvailable = g.subNat C)
    (hstep : Xstep vj s
              = if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
                else .ok (s', .some (.revert, o)))
    (hk : k ≤ C) (hC : C + cost ≤ g.toNat) :
    X (g.toNat + 1 - k) vj s = .ok (.revert s'.machineState.gasAvailable.toUInt256 o) := by
  have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel]
  have hgg : ¬ (s.machineState.gasAvailable.toNat < cost) := by rw [hgas]; simp [Sat256.subNat, Sat256.toNat] at *; omega
  exact Xstep_X_X_halt_revert _ s s' vj o (by rw [hstep]; simp [hgg])

/-! ## 3¾. Coverage helpers — build a `runtimeEquivalenceFor` case from a `Ξ` outcome -/

/-- `Ξ` runs out of gas ⇒ the `outOfGas` case. -/
theorem reEquiv_outOfGas {cfg contract cA gh bl σ_evm σ_solm σ₀ g A I}
    (h : Ξ cA gh bl σ_evm σ₀ g A I = .error .OutOfGass) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  .outOfGas h

/-- When a contract has no `receive`/`fallback`, a successful `dispatchMsg` is a successful
    selector dispatch: the receive and fallback arms of `dispatchMsg` are `none`.  Shared by the
    `decodingFailed`/`execution` coverage helpers below. -/
theorem selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some
    {contract : ContractDecl} {calldata : ByteArray} {transition : TransitionDecl}
    (hreceive : contract.receive = none)
    (hfallback : contract.fallback = none)
    (h : dispatchMsg contract calldata = some transition) :
    selectorDispatchMsg contract calldata = some transition := by
  unfold dispatchMsg at h
  cases hsel : selectorDispatchMsg contract calldata with
  | none =>
      have hreceiveDispatch : receiveDispatchMsg contract calldata = none := by
        simp [receiveDispatchMsg, hreceive]
      rw [hsel, hreceiveDispatch, hfallback] at h
      simp at h
  | some selected =>
      rw [hsel] at h
      simpa using h

/-- Solm fails to dispatch and `Ξ` reverts ⇒ the `noDispatch` case.  The Solm-side maps are
    unconstrained — this path never runs `solmExec`. -/
theorem reEquiv_noDispatch {cfg contract cA gh bl σ_evm σ_solm σ₀ g A I} {g' o}
    (hd : dispatchMsg contract I.calldata = none)
    (h : Ξ cA gh bl σ_evm σ₀ g A I = .ok (.revert g' o)) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  .noDispatch hd h

/-- Solm dispatches but decoding fails and `Ξ` reverts ⇒ `decodingFailed`. Solm-side maps
    unconstrained. -/
theorem reEquiv_decodingFailed
    {cfg contract cA gh bl σ_evm σ_solm σ₀ g A I} {t g' o}
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none)
    (h : Ξ cA gh bl σ_evm σ₀ g A I = .ok (.revert g' o))
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  .decodingFailed (selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some hreceive hfallback hd)
    rfl hdec h

/-- The Solm transition executes (to `actRes`) and `Ξ`'s result matches ⇒ the `execution` case.
    The EVM runs from `σ_evm`, the Solm body from `σ_solm` (genuinely distinct maps); `hequiv`
    carries the up-to-`accountMapEquiv` coupling of their results. -/
theorem reEquiv_execution
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {t callargs actRes}
    {g : UInt256}
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ (.ofUInt256 g) A I) callargs t.body actRes)
    (hequiv : execResultsEquiv (Ξ cA gh bl σ_evm σ₀ g A I) actRes (.abi t.returnType))
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  .execution rfl
    (.intro (selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some hreceive hfallback hd)
      rfl hdec rfl hbody)
    hequiv

/-- The receive transition executes without selector ABI decoding and `Ξ`'s result matches. -/
theorem reEquiv_receiveExecution
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {t actRes}
    {g : UInt256}
    (hreceive : receiveDispatchMsg contract I.calldata = some t)
    (hparams : t.params = [])
    (hreturn : t.returnType = [])
    (hbody : ExecTransitionBody cfg contract
              (initState cA gh bl σ_solm σ₀ (.ofUInt256 g) A I) ∅ t.body actRes)
    (hequiv : execResultsEquiv (Ξ cA gh bl σ_evm σ₀ g A I) actRes (.abi [])) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I :=
  .execution rfl (.receive hreceive hparams hreturn rfl hbody) hequiv

/-! ## 4. Fuel monotonicity -/

end Reasoning.Theory
