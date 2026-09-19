import EVMReasoning.Reach
import Solm.Equiv

/-!
# Sol⁻-coupled reach rules

The coupled loop rule and the `runtimeEquivalenceFor` builders that used to live in `Reasoning/Reach.lean`;
everything here mentions Sol⁻ semantics or its refinement relation.
-/

set_option maxRecDepth 10000

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Reach

open Reasoning.Theory

-- Private in `EVMReasoning/Reach.lean`; replicated for the eliminators below.
private theorem Xi_error_of_X_sat
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {e} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) = .error e) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .error e :=
  Xi_error_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

private theorem Xi_revert_of_X_sat
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g' o} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          = .ok (.revert g' o)) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .ok (.revert g' o) :=
  Xi_revert_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

private theorem Xi_success_of_X_sat
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {s' o} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          = .ok (.success s' o)) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I
      = .ok (.success (s'.createdAccounts, s'.accountMap, s'.machineState.gasAvailable.toUInt256,
                       s'.substate) o) :=
  Xi_success_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

/-- Coupled variant-indexed loop rule for a solc bytecode loop and a Solm `for` loop.

This is the `RD.whileLoopCarryFull` analogue used when the source loop body may revert before the
variant reaches zero.  The caller supplies the bytecode transitions for the false-condition exit
and the true-condition body entry, plus a body step that either reverts both sides or produces the
next carried state. -/
theorem RD.execForLoopOrRevertCarryFull {cfg : Config} {contract : ContractDecl}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (header bodyHeader exit : UInt256) (condExpr : Expr) (post body : List Stmt)
    (Inv : ℕ → α → Store → EVM.State → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256)
    (hfalse : ∀ a L evm, Inv 0 a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool false))
    (hexit : ∀ a L evm, Inv 0 a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) rdata (acc a) k' C')
    (htrue : ∀ v a L evm, Inv (v + 1) a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool true))
    (henter : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C', RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k' C')
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k C →
      (ExecBlock cfg { contract := contract, locals := L } evm body .reverted ∧
        RDrev code g s0) ∨
      ∃ a' L1 evm1 L2 evm2 k' C',
        (ExecBlock cfg { contract := contract, locals := L } evm body
            (.ok { contract := contract, locals := L1 } evm1) ∨
          ExecBlock cfg { contract := contract, locals := L } evm body
            (.continue { contract := contract, locals := L1 } evm1)) ∧
        ExecBlock cfg { contract := contract, locals := L1 } evm1 post
          (.ok { contract := contract, locals := L2 } evm2) ∧
        Inv v a' L2 evm2 ∧
        RD code ee g s0 header (stk a') (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecForLoop cfg { contract := contract, locals := L } evm condExpr post body
          (.ok { contract := contract, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD code ee g s0 exit (exitStk a') (mem a') (aw a') rdata (acc a') k' C') ∨
      (ExecForLoop cfg { contract := contract, locals := L } evm condExpr post body .reverted ∧
        RDrev code g s0) := by
  intro v
  induction v with
  | zero =>
      intro a L evm hInv k C rd
      obtain ⟨k', C', rdExit⟩ := hexit a L evm hInv k C rd
      exact Or.inl ⟨a, L, evm, k', C', ExecForLoop.falseDone (hfalse a L evm hInv),
        hInv, rdExit⟩
  | succ v ih =>
      intro a L evm hInv k C rd
      obtain ⟨k1, C1, rdBody⟩ := henter v a L evm hInv k C rd
      rcases hbody v a L evm hInv k1 C1 rdBody with hrev | hstep
      · exact Or.inr ⟨ExecForLoop.bodyRevert (htrue v a L evm hInv) hrev.1, hrev.2⟩
      · rcases hstep with
          ⟨a', L1, evm1, L2, evm2, k2, C2, hbodyStep, hpost, hInv', rdNext⟩
        rcases ih a' L2 evm2 hInv' k2 C2 rdNext with hdone | hloopRev
        · rcases hdone with ⟨a'', L', evm', k', C', hloop, hInv0, rdExit⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact Or.inl ⟨a'', L', evm', k', C',
              ExecForLoop.iterate (htrue v a L evm hInv) hbodyOk hpost hloop,
              hInv0, rdExit⟩
          · exact Or.inl ⟨a'', L', evm', k', C',
              ExecForLoop.continueIter (htrue v a L evm hInv) hbodyCont hpost hloop,
              hInv0, rdExit⟩
        · rcases hloopRev with ⟨hloop, hrdRev⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact Or.inr
              ⟨ExecForLoop.iterate (htrue v a L evm hInv) hbodyOk hpost hloop, hrdRev⟩
          · exact Or.inr
              ⟨ExecForLoop.continueIter (htrue v a L evm hInv) hbodyCont hpost hloop,
                hrdRev⟩

end Reasoning.Reach

namespace Reasoning.Theory

/-! ## Coverage helpers — build a `runtimeEquivalenceFor` case from a `Ξ` outcome -/

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

end Reasoning.Theory

namespace Reasoning.Reach

open Reasoning.Theory

/-! ## From RD terminals to Solm runtime-equivalence

`RDret`/`RDrev` record that the *whole* run `X (g+1) … (initState …)` halts.  These
eliminators carry that halting fact across the `X → Ξ` bridge (`Xi_*_of_X`) and into a
`runtimeEquivalenceFor` case, folding the out-of-gas alternative into `reEquiv_outOfGas`
*once*.  A revert/success segment therefore reaches the Solm layer compositionally — e.g.
`(powX_short …).reEquivNoDispatch hcode (powDispatch_none_short …)` — with no per-site
`rcases` / `Xi_*_of_X` / `reEquiv_*` plumbing.  All four are contract- and bytecode-generic
(`hcode : I.code = code` bridges the concrete bytecode back to `I.code`). -/

/-- Eliminate an `RDrev` into a `runtimeEquivalenceFor`: the OOG alternative becomes the
    `outOfGas` case automatically, and the continuation `k` receives the `Ξ`-level revert. -/
theorem RDrev.reEquivElim
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (k : ∀ g' o,
          Ξ cA gh bl σ_evm σ₀ g.toUInt256 A I = .ok (.revert g' o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
            g.toUInt256 A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hX⟩
  · exact reEquiv_outOfGas (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · exact k g' o (Xi_revert_of_X_sat (by rw [← hcode] at hX; exact hX))

/-- `RDrev ⇒ noDispatch`: revert with Act failing to dispatch. Solm-side maps unconstrained. -/
theorem RDrev.reEquivNoDispatch
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_noDispatch hd hrev

/-- `RDrev ⇒ decodingFailed`: Act dispatches to `t` but calldata-decoding fails.  Solm-side maps
    unconstrained. -/
theorem RDrev.reEquivDecodingFailed
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray} {t}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_decodingFailed hd hdec hrev hfallback hreceive

/-- Eliminate an `RDret` into a `runtimeEquivalenceFor`: the OOG alternative becomes the
    `outOfGas` case automatically; the continuation `k` receives the `Ξ`-level success, with
    accounts already projected back to the carried `(cA, σ_evm)`. -/
theorem RDret.reEquivElim
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code o : ByteArray}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (k : ∀ (g' : UInt256) (A' : Substate),
          Ξ cA gh bl σ_evm σ₀ g.toUInt256 A I = .ok (.success (cA, σ_evm, g', A') o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
            g.toUInt256 A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ_evm := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X_sat (by rw [← hcode] at hX; exact hX)
    rw [hcA, hσ] at hxi
    exact k _ _ hxi

end Reasoning.Reach
