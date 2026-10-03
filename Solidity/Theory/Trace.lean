import Solidity.Equiv
import Solidity.Theory.Body
import EVMReasoning.SolcIdioms
import Ethereum.Theory.StorageExtensionality

/-!
# From `Run` traces to the refinement relation

The terminal facts of `Reasoning.Trace` (`Returned`, `Reverted`) at a transaction's `initState`
give the `Ξ`-level outcome with the final world and the exact revert data; paired with a
`solidityExec` derivation they discharge one case of `runtimeEquivalenceFor` (accounts, return
data, revert data and logs).  Also here: the bridges from solc's revert payloads
(`solcPanicPayload`, `solcErrorStringPayload`) to the spec's (`panicData`, `errorStringData`),
the exact `LogEntry` of a value-type event, and the dispatcher-level cases (non-payable, short
calldata, no matching selector).  Out-of-gas is absorbed by every bridge.
-/

namespace Solidity

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Trace
open Reasoning.Reach (armWellFormed armSelNat nthArmPc solcDispatchPrefixWellFormed solcGuardTgt
  solcGuardTgtOp solcGuardTgtWidth solcGuardJumpiPc solcCalldataRevertTgt solcCalldataRevertTgtOp
  solcCalldataRevertTgtWidth solcSlotWord)

/-! ## Machines -/

theorem initMachine_evm {cA gh bl σ σ₀ g A I} (h : Heap) :
    (initMachine cA gh bl σ σ₀ g A I h).evm = initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I := rfl

@[simp] theorem pushLog_evm_accountMap (m : Machine) (le : LogEntry) :
    (m.pushLog le).evm.accountMap = m.evm.accountMap := rfl
@[simp] theorem pushLog_evm_createdAccounts (m : Machine) (le : LogEntry) :
    (m.pushLog le).evm.createdAccounts = m.evm.createdAccounts := rfl
@[simp] theorem pushLog_evm_executionEnv (m : Machine) (le : LogEntry) :
    (m.pushLog le).evm.executionEnv = m.evm.executionEnv := rfl
@[simp] theorem pushLog_logSeries (m : Machine) (le : LogEntry) :
    (m.pushLog le).evm.substate.logSeries = m.evm.substate.logSeries.push le := rfl
@[simp] theorem pushLog_heap (m : Machine) (le : LogEntry) : (m.pushLog le).heap = m.heap := rfl
@[simp] theorem pushLog_this (m : Machine) (le : LogEntry) : (m.pushLog le).this = m.this := rfl

@[simp] theorem initMachine_executionEnv {cA gh bl σ σ₀ g A I} (h : Heap) :
    (initMachine cA gh bl σ σ₀ g A I h).evm.executionEnv = I := rfl

/-- The `uint256` word at `slot`. -/
abbrev loadU256 (m : Machine) (slot : UInt256) : UInt256 :=
  Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner slot

/-- The machine after storing `w` into the `uint256` slot `slot`. -/
abbrev storeU256 (m : Machine) (slot w : UInt256) : Machine :=
  { m with evm := Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot w }

attribute [simp] storageStore_executionEnv

@[simp] theorem storeU256_executionEnv (m : Machine) (slot w : UInt256) :
    (storeU256 m slot w).evm.executionEnv = m.evm.executionEnv :=
  storageStore_executionEnv ..
@[simp] theorem storeU256_heap (m : Machine) (slot w : UInt256) : (storeU256 m slot w).heap = m.heap := rfl
@[simp] theorem storeU256_this (m : Machine) (slot w : UInt256) : (storeU256 m slot w).this = m.this :=
  congrArg ExecutionEnv.codeOwner (storageStore_executionEnv ..)
@[simp] theorem storeU256_logSeries (m : Machine) (slot w : UInt256) :
    (storeU256 m slot w).evm.substate.logSeries = m.evm.substate.logSeries := by
  show (Storage.EVM.storageStore m.evm _ slot w).substate.logSeries = _
  rw [storageStore_substate]

/-- Any oracle serves a run without external calls or `gasleft()`. -/
instance : Inhabited Oracle :=
  ⟨{ gasleft := fun _ => ⟨0⟩, callGas := fun _ => ⟨0⟩, substateIn := fun _ => default }⟩

/-! ## World transport

The trace world and the spec machine agree on the observables of `execResultsEquiv`; the relation
is preserved by the storage writes and log pushes both sides perform in lockstep. -/

structure WorldEquiv (w : World) (m : Machine) : Prop where
  created : w.created = m.evm.createdAccounts
  accounts : Refinement.accountMapEquiv w.accounts m.evm.accountMap
  logs : w.logs = m.evm.substate.logSeries

namespace WorldEquiv

theorem init {cA gh bl σ_evm σ_spec σ₀ g A I} (h : Heap) (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    WorldEquiv ⟨cA, σ_evm, A.logSeries⟩ (initMachine cA gh bl σ_spec σ₀ g A I h) :=
  ⟨rfl, hAccounts, rfl⟩

/-- `SSTORE` on the trace side, `storeU256` on the spec side. -/
theorem sstore {w : World} {m : Machine} (h : WorldEquiv w m) {owner : AccountAddress}
    (hown : owner = m.evm.executionEnv.codeOwner) (slot val : UInt256) :
    WorldEquiv { w with accounts := sstoreAccountMap owner w.accounts slot val } (storeU256 m slot val) := by
  subst hown
  refine ⟨?_, ?_, ?_⟩
  · show w.created = (Storage.EVM.storageStore m.evm _ slot val).createdAccounts
    rw [storageStore_createdAccounts]; exact h.created
  · show Refinement.accountMapEquiv (sstoreAccountMap _ w.accounts slot val)
      (Storage.EVM.storageStore m.evm _ slot val).accountMap
    rw [storageStore_accountMap]; exact accountMapEquiv_sstoreAccountMap _ slot val h.accounts
  · show w.logs = (Storage.EVM.storageStore m.evm _ slot val).substate.logSeries
    rw [storageStore_substate]; exact h.logs

/-- `SLOAD` on the trace side reads the spec machine's word. -/
theorem sload {w : World} {m : Machine} (h : WorldEquiv w m) {I : ExecutionEnv}
    (hown : I.codeOwner = m.evm.executionEnv.codeOwner) (slot : UInt256) :
    solcSlotWord w.accounts I slot = loadU256 m slot := by
  rw [solcSlotWord, hown]
  show _ = (m.evm.accountMap.find? _).option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)
  exact accountMapEquiv_storage_findD h.accounts _ slot ⟨0⟩

theorem pushLog {w : World} {m : Machine} (h : WorldEquiv w m) (le : LogEntry) :
    WorldEquiv { w with logs := w.logs.push le } (m.pushLog le) :=
  ⟨h.created, h.accounts, by rw [pushLog_logSeries, h.logs]⟩

end WorldEquiv

/-! ## External calls

An EVM `CALL` (`Run.call`, exposing `callTheta`) and the spec's `callViaEVM` invoke `Θ` on
extensionally equal account maps with the same arguments, so their results coincide up to
`accountMapEquiv`; the oracle supplies the substate and gas the trace witnessed. -/

theorem accountAddress_roundtrip (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hlt : a.val < AccountAddress.size := a.isLt
  have hv : ((UInt256.ofNat a.val).val : ℕ) = a.val := by
    show ((Fin.ofNat _ a.val) : Fin UInt256.size).val = a.val
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_trans hlt hsize)
  apply Fin.ext
  simp only [AccountAddress.ofUInt256, Fin.ofNat, hv]
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

theorem accountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : Refinement.accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;> simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

theorem accountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : Refinement.accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;> simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

@[simp] theorem calleeGas_none_zero (o : Oracle) (m : Machine) : calleeGas o m none 0 = o.callGas m.tick := rfl

@[simp] theorem afterCall_executionEnv (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').evm.executionEnv = m.evm.executionEnv := rfl
@[simp] theorem afterCall_heap (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').heap = m.heap := rfl
@[simp] theorem afterCall_this (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').this = m.this := rfl
@[simp] theorem afterCall_tick (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').tick = m.tick + 1 := rfl
@[simp] theorem afterCall_accountMap (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').evm.accountMap = σ' := rfl
@[simp] theorem afterCall_createdAccounts (m : Machine) (cA' : Batteries.RBSet AccountAddress compare)
    (σ' : AccountMap) (A' : Substate) : (afterCall m cA' σ' A').evm.createdAccounts = cA' := rfl
@[simp] theorem afterCall_logSeries (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').evm.substate.logSeries = A'.logSeries := rfl
@[simp] theorem afterCall_genesisBlockHeader (m : Machine) (cA' : Batteries.RBSet AccountAddress compare)
    (σ' : AccountMap) (A' : Substate) : (afterCall m cA' σ' A').evm.genesisBlockHeader = m.evm.genesisBlockHeader := rfl
@[simp] theorem afterCall_blocks (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').evm.blocks = m.evm.blocks := rfl
@[simp] theorem afterCall_σ₀ (m : Machine) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) : (afterCall m cA' σ' A').evm.σ₀ = m.evm.σ₀ := rfl

/-- The oracle's sub-call substate is the one the trace witnessed once their log series agree. -/
theorem subInput_eq {o : Oracle} {m : Machine} {A_in : Substate} (hsub : o.substateIn m.tick = A_in)
    (hlogs : A_in.logSeries = m.evm.substate.logSeries) : subInput o m = A_in := by
  unfold subInput
  rw [hsub, ← hlogs]

/-- **Call made.**  The `Θ` link of a value-free `CALL`/`STATICCALL` (`callTheta` / `staticcallTheta`
    with `perm` the flag the opcode passes) is a spec `callViaEVM` step on the equivalent machine,
    with the oracle's substate and gas fixed to the trace's witnesses; the worlds stay related. -/
theorem WorldEquiv.callMade {s0 : State} {w : World} {m : Machine} {o : Oracle} {A_in A' : Substate}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {g'' target callGas : UInt256}
    {z perm : Bool} {out input : ByteArray}
    (hw : WorldEquiv w m)
    (hΘ : (cA', σ', g'', A', z, out) =
      Ethereum.EVM.Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks w.accounts
        s0.σ₀ A_in (AccountAddress.ofUInt256 (UInt256.ofNat s0.executionEnv.codeOwner)) s0.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute w.accounts (AccountAddress.ofUInt256 target)) callGas
        (UInt256.ofNat s0.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩ input (s0.executionEnv.depth + 1)
        s0.executionEnv.header perm)
    (hlogs : A_in.logSeries = w.logs) (hsub : o.substateIn m.tick = A_in)
    (henv : m.evm.executionEnv = s0.executionEnv) (hgh : m.evm.genesisBlockHeader = s0.genesisBlockHeader)
    (hbl : m.evm.blocks = s0.blocks) (hσ₀ : m.evm.σ₀ = s0.σ₀) (hdepth : s0.executionEnv.depth ≠ 1024) :
    ∃ σs : AccountMap,
      callViaEVM o m (AccountAddress.ofUInt256 target) 0 input perm callGas (z, afterCall m cA' σs A', out) ∧
      WorldEquiv ⟨cA', σ', A'.logSeries⟩ (afterCall m cA' σs A') := by
  have hext : accountMapExtensionalEq w.accounts m.evm.accountMap :=
    accountMapExtensionalEq_of_accountMapEquiv hw.accounts
  have hsubIn : subInput o m = A_in := subInput_eq hsub (hlogs.trans hw.logs)
  rw [accountAddress_roundtrip] at hΘ
  generalize hres : Ethereum.EVM.Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks
      m.evm.accountMap s0.σ₀ A_in s0.executionEnv.codeOwner s0.executionEnv.sender
      (AccountAddress.ofUInt256 target) (toExecute w.accounts (AccountAddress.ofUInt256 target)) callGas
      (UInt256.ofNat s0.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩ input (s0.executionEnv.depth + 1)
      s0.executionEnv.header perm = res
  obtain ⟨cAs, σs, gs, As, zs, outs⟩ := res
  obtain ⟨hcA, hg, hA, hz, hout, hσ⟩ :=
    (accountMap_extensionality_of_Theta_and_Lambda (i := ByteArray.empty) (ζ := none) 0 0 _ cA' cAs σ' σs g'' gs
      A' As z zs out outs _ hext).1 hΘ.symm hres
  subst hcA hg hA hz hout
  refine ⟨σs, ?_, ⟨rfl, accountMapEquiv_of_accountMapExtensionalEq hσ, rfl⟩⟩
  refine callViaEVM.callMade (valueWord := ⟨0⟩) (g' := g'') (by decide) (Fin.zero_le _) (by rw [henv]; exact hdepth) ?_
  simp only [Machine.this, henv, hgh, hbl, hσ₀, hsubIn, ← hw.created,
    ← accountMapExtensionalEq_toExecute hext (AccountAddress.ofUInt256 target)]
  exact hres.symm

/-- **Call not made** at the depth limit: the spec's `callNotMade` step; the world is unchanged. -/
theorem WorldEquiv.callNotMade {w : World} {m : Machine} (hw : WorldEquiv w m) (o : Oracle)
    (target : AccountAddress) (input : ByteArray) (perm : Bool) (gas : UInt256)
    (hdepth : m.evm.executionEnv.depth = 1024) :
    callViaEVM o m target 0 input perm gas
        (false, { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 }, ByteArray.empty) ∧
      WorldEquiv w { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 } :=
  ⟨callViaEVM.callNotMade (valueWord := ⟨0⟩) (by decide) (Or.inr hdepth), ⟨hw.created, hw.accounts, hw.logs⟩⟩

theorem accountMapEquiv_balance {σ τ : AccountMap} (h : Refinement.accountMapEquiv σ τ) (a : AccountAddress) :
    (σ.find? a).elim ⟨0⟩ (·.balance) = (τ.find? a).elim ⟨0⟩ (·.balance) := by
  specialize h a
  cases hσ : σ.find? a <;> cases hτ : τ.find? a <;> simp [hσ, hτ] at h ⊢
  exact h.2.1

theorem balance_getD_default (σ : AccountMap) (a : AccountAddress) :
    ((σ.find? a).getD default).balance = (σ.find? a).elim ⟨0⟩ (·.balance) := by
  cases σ.find? a
  · show (default : Account).balance = ⟨0⟩
    rfl
  · rfl

/-- **Call made with value** (`Run.callValueMade`): as `callMade`, the balance check discharged
    on the trace side. -/
theorem WorldEquiv.callMadeValue {s0 : State} {w : World} {m : Machine} {o : Oracle} {A_in A' : Substate}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {g'' target callGas valueWord : UInt256}
    {value : ℕ} {z perm : Bool} {out input : ByteArray}
    (hw : WorldEquiv w m) (hvw : valueWord = EVM.Word.ofNat value)
    (hΘ : (cA', σ', g'', A', z, out) =
      Ethereum.EVM.Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks w.accounts
        s0.σ₀ A_in (AccountAddress.ofUInt256 (UInt256.ofNat s0.executionEnv.codeOwner)) s0.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute w.accounts (AccountAddress.ofUInt256 target)) callGas
        (UInt256.ofNat s0.executionEnv.gasPrice) valueWord valueWord input (s0.executionEnv.depth + 1)
        s0.executionEnv.header perm)
    (hbal : valueWord ≤ (w.accounts.find? s0.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hlogs : A_in.logSeries = w.logs) (hsub : o.substateIn m.tick = A_in)
    (henv : m.evm.executionEnv = s0.executionEnv) (hgh : m.evm.genesisBlockHeader = s0.genesisBlockHeader)
    (hbl : m.evm.blocks = s0.blocks) (hσ₀ : m.evm.σ₀ = s0.σ₀) (hdepth : s0.executionEnv.depth ≠ 1024) :
    ∃ σs : AccountMap,
      callViaEVM o m (AccountAddress.ofUInt256 target) value input perm callGas (z, afterCall m cA' σs A', out) ∧
      WorldEquiv ⟨cA', σ', A'.logSeries⟩ (afterCall m cA' σs A') := by
  have hext : accountMapExtensionalEq w.accounts m.evm.accountMap :=
    accountMapExtensionalEq_of_accountMapEquiv hw.accounts
  have hsubIn : subInput o m = A_in := subInput_eq hsub (hlogs.trans hw.logs)
  have hbal' : valueWord ≤ ((m.evm.accountMap.find? m.this).getD default).balance := by
    rw [balance_getD_default, Machine.this, henv, ← accountMapEquiv_balance hw.accounts]
    exact hbal
  rw [accountAddress_roundtrip] at hΘ
  generalize hres : Ethereum.EVM.Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks
      m.evm.accountMap s0.σ₀ A_in s0.executionEnv.codeOwner s0.executionEnv.sender
      (AccountAddress.ofUInt256 target) (toExecute w.accounts (AccountAddress.ofUInt256 target)) callGas
      (UInt256.ofNat s0.executionEnv.gasPrice) valueWord valueWord input (s0.executionEnv.depth + 1)
      s0.executionEnv.header perm = res
  obtain ⟨cAs, σs, gs, As, zs, outs⟩ := res
  obtain ⟨hcA, hg, hA, hz, hout, hσ⟩ :=
    (accountMap_extensionality_of_Theta_and_Lambda (i := ByteArray.empty) (ζ := none) 0 0 _ cA' cAs σ' σs g'' gs
      A' As z zs out outs _ hext).1 hΘ.symm hres
  subst hcA hg hA hz hout
  refine ⟨σs, ?_, ⟨rfl, accountMapEquiv_of_accountMapExtensionalEq hσ, rfl⟩⟩
  refine callViaEVM.callMade (valueWord := valueWord) (g' := g'') hvw hbal' (by rw [henv]; exact hdepth) ?_
  simp only [Machine.this, henv, hgh, hbl, hσ₀, hsubIn, ← hw.created,
    ← accountMapExtensionalEq_toExecute hext (AccountAddress.ofUInt256 target)]
  exact hres.symm

/-- **Call not made for lack of balance** (`Run.callValueInsufficientBalance`): the spec's
    `callNotMade`; the world is unchanged. -/
theorem WorldEquiv.callNotMadeBalance {s0 : State} {w : World} {m : Machine} (hw : WorldEquiv w m) (o : Oracle)
    {valueWord : UInt256} {value : ℕ} (hvw : valueWord = EVM.Word.ofNat value)
    (target : AccountAddress) (input : ByteArray) (perm : Bool) (gas : UInt256)
    (henv : m.evm.executionEnv = s0.executionEnv)
    (hbal : ¬ valueWord ≤ (w.accounts.find? s0.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) :
    callViaEVM o m target value input perm gas
        (false, { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 }, ByteArray.empty) ∧
      WorldEquiv w { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 } := by
  have hgt : valueWord > ((m.evm.accountMap.find? m.this).getD default).balance := by
    rw [balance_getD_default, Machine.this, henv, ← accountMapEquiv_balance hw.accounts]
    exact Nat.lt_of_not_le hbal
  exact ⟨callViaEVM.callNotMade (valueWord := valueWord) hvw (Or.inl hgt), ⟨hw.created, hw.accounts, hw.logs⟩⟩

theorem address_toNat (a : EVM.Address) : EVM.address a.toNat = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

theorem toUTF8_empty : "".toUTF8 = ByteArray.empty := by native_decide

/-! ## Custom errors -/

theorem customErrorData_nil (sigStr : String) : customErrorData sigStr [] [] = some (selectorOf sigStr) := by
  simp [customErrorData, ABI.encodeCallWithSelector?, ABI.encodeABIValues?, ABI.abiTupleHeadSize?,
    ABI.encodeABIValuesFrom?]

theorem customErrorData_u256 (sigStr : String) (n : ℕ) (hn : n < 2 ^ 256) :
    customErrorData sigStr [.elem (.int (.uint ⟨256, by decide⟩))] [.int n] =
      some (selectorOf sigStr ++ UInt256.toByteArray (UInt256.ofNat n)) := by
  have hn' : n < EVM.twoPow 256 := hn
  simp [customErrorData, ABI.encodeCallWithSelector?, ABI.encodeABIValues?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
    ABI.encodeABIWord?, hn', word_toBytesBE_toByteArray_eq_toByteArray]
  rfl

/-! ## Message calls -/

/-- A returned run + a returning spec run (world related, return data encoded) ⇒ `execution`. -/
theorem Returned.specExecution {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code out : ByteArray}
    {w : World} {m : Machine} {vs conv}
    (o : Oracle) (hcode : I.code = code)
    (h : Returned code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) w out)
    (hspec : solidityExec cfg o fc cA gh bl σ_spec σ₀ g A I (.returned m vs) conv)
    (hCreated : w.created = m.evm.createdAccounts)
    (hAccounts : Refinement.accountMapEquiv w.accounts m.evm.accountMap)
    (hLogs : w.logs = m.evm.substate.logSeries)
    (henc : returnDataEquiv out vs conv) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I := by
  rcases Returned.xi hcode h with hoog | ⟨g', A', hxi, hlogs⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .success rfl rfl hCreated hAccounts (hlogs.trans hLogs) henc⟩

/-- `Returned.specExecution` with the world facts bundled as `WorldEquiv`. -/
theorem Returned.specExecutionW {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code out : ByteArray}
    {w : World} {m : Machine} {vs conv}
    (o : Oracle) (hcode : I.code = code)
    (h : Returned code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) w out)
    (hspec : solidityExec cfg o fc cA gh bl σ_spec σ₀ g A I (.returned m vs) conv)
    (hw : WorldEquiv w m) (henc : returnDataEquiv out vs conv) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Returned.specExecution o hcode h hspec hw.created hw.accounts hw.logs henc

/-- A reverted run + a spec run reverting with the same data ⇒ `execution`. -/
theorem Reverted.specRevert {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code d : ByteArray} {conv}
    (o : Oracle) (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) d)
    (hspec : solidityExec cfg o fc cA gh bl σ_spec σ₀ g A I (.reverted d) conv) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I := by
  rcases Reverted.xi hcode h with hoog | ⟨g', hxi⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .revert rfl rfl⟩

/-- An empty revert when the spec accepts no entry point ⇒ `noDispatch`. -/
theorem Reverted.specNoDispatch {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty)
    (hd : dispatches fc I.calldata = false) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I := by
  rcases Reverted.xi hcode h with hoog | ⟨g', hxi⟩
  · exact .outOfGas hoog
  · exact .noDispatch hd hxi

/-- An empty revert when the spec dispatches but cannot decode the arguments ⇒ `decodingFailed`. -/
theorem Reverted.specDecodingFailed {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code : ByteArray}
    {e : DispatchEntry} {fn : FnDef}
    (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty)
    (he : selectorDispatch fc I.calldata = some e) (hfn : fc.fns[e.fn]? = some fn)
    (hpay : payableOrNoValue fn.decl I)
    (hdec : decodeArgs cfg fc.types fn.decl I.calldata = none) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I := by
  rcases Reverted.xi hcode h with hoog | ⟨g', hxi⟩
  · exact .outOfGas hoog
  · exact .decodingFailed he hfn hpay hdec hxi (Or.inl rfl)

/-- A `Panic(0x41)` revert from the argument decoder of a function with a dynamic memory parameter,
    when the spec dispatches but cannot decode the arguments ⇒ `decodingFailed`. -/
theorem Reverted.specDecodingPanic {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code : ByteArray}
    {e : DispatchEntry} {fn : FnDef}
    (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (panicData 0x41))
    (he : selectorDispatch fc I.calldata = some e) (hfn : fc.fns[e.fn]? = some fn)
    (hpay : payableOrNoValue fn.decl I)
    (hdec : decodeArgs cfg fc.types fn.decl I.calldata = none)
    (hmem : hasDynamicMemoryParam fc.types fn.decl = true) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I := by
  rcases Reverted.xi hcode h with hoog | ⟨g', hxi⟩
  · exact .outOfGas hoog
  · exact .decodingFailed he hfn hpay hdec hxi (Or.inr ⟨hmem, rfl⟩)

/-! ## Constructors -/

/-- The initcode returning the runtime code + a successful spec construction. -/
theorem Returned.specCtor {cfg fc args cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code out : ByteArray}
    {w : World} {m : Machine} {imms : Store} {runtimeCodeOf : Store → Option ByteArray}
    (o : Oracle) (hcode : I.code = code)
    (h : Returned code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) w out)
    (hspec : solidityCtorExec cfg o fc args cA gh bl σ_spec σ₀ g A I (.ok m imms))
    (hCreated : w.created = m.evm.createdAccounts)
    (hAccounts : Refinement.accountMapEquiv w.accounts m.evm.accountMap)
    (hLogs : w.logs = m.evm.substate.logSeries)
    (hout : runtimeCodeOf imms = some out) :
    constructorEquivalenceFor cfg fc args cA gh bl σ_evm σ_spec σ₀ g A I runtimeCodeOf := by
  rcases Returned.xi hcode h with hoog | ⟨g', A', hxi, hlogs⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .success rfl rfl hCreated hAccounts (hlogs.trans hLogs) hout⟩

/-- `Returned.specCtor` with the world facts bundled as `WorldEquiv`. -/
theorem Returned.specCtorW {cfg fc args cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code out : ByteArray}
    {w : World} {m : Machine} {imms : Store} {runtimeCodeOf : Store → Option ByteArray}
    (o : Oracle) (hcode : I.code = code)
    (h : Returned code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) w out)
    (hspec : solidityCtorExec cfg o fc args cA gh bl σ_spec σ₀ g A I (.ok m imms))
    (hw : WorldEquiv w m) (hout : runtimeCodeOf imms = some out) :
    constructorEquivalenceFor cfg fc args cA gh bl σ_evm σ_spec σ₀ g A I runtimeCodeOf :=
  Returned.specCtor o hcode h hspec hw.created hw.accounts hw.logs hout

/-- The initcode reverting + a spec construction reverting with the same data. -/
theorem Reverted.specCtorRevert {cfg fc args cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code d : ByteArray}
    {runtimeCodeOf : Store → Option ByteArray}
    (o : Oracle) (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) d)
    (hspec : solidityCtorExec cfg o fc args cA gh bl σ_spec σ₀ g A I (.reverted d)) :
    constructorEquivalenceFor cfg fc args cA gh bl σ_evm σ_spec σ₀ g A I runtimeCodeOf := by
  rcases Reverted.xi hcode h with hoog | ⟨g', hxi⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .revert rfl rfl⟩

/-! ## Revert payloads -/

theorem panicSelector_eq : (UInt256.toByteArray solcPanicSelectorWord).extract 0 4 = panicSelector := by
  native_decide

theorem errorStringSelector_eq :
    (UInt256.toByteArray solcErrorStringSelector).extract 0 4 = errorStringSelector := by
  native_decide

/-- solc's `Panic(code)` bytes are the spec's. -/
theorem solcPanicPayload_eq (c : UInt256) : solcPanicPayload c = panicData c.toNat := by
  unfold solcPanicPayload panicData
  rw [u256_ofNat_toNat, panicSelector_eq]

theorem panicData_eq (n : ℕ) (hn : n < UInt256.size) :
    panicData n = solcPanicPayload (UInt256.ofNat n) := by
  rw [solcPanicPayload_eq, ulit_toNat' n hn]

theorem Panic.data_eq (p : Panic) : p.data = solcPanicPayload (UInt256.ofNat p.code) :=
  panicData_eq p.code (by cases p <;> decide)

theorem list_toByteArray_eq (l : List UInt8) : l.toByteArray = ⟨l.toArray⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]

theorem byteArray_toList_toByteArray (b : ByteArray) : b.toList.toByteArray = b := by
  rw [byteArray_toList_eq, list_toByteArray_eq, Array.toArray_toList]

theorem natBytes_toByteArray (n : ℕ) :
    (ABI.natBytes n).toByteArray = UInt256.toByteArray (UInt256.ofNat n) :=
  word_toBytesBE_toByteArray_eq_toByteArray (UInt256.ofNat n)

/-- The ABI encoding of one `string` argument: offset word, length word, padded data. -/
theorem encodeABIValues_string (b : ByteArray) :
    ABI.encodeABIValues? [.string] [.bytes b] =
      some (ABI.natBytes 32 ++ (ABI.natBytes b.size ++ ABI.padRightToWord b.toList)) := by
  simp [ABI.encodeABIValues?, ABI.abiTupleHeadSize?, ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
    ABI.isDynamicABIType]

theorem padRightToWord_toByteArray (b : ByteArray) (hpos : 0 < b.size) (hle : b.size ≤ 32) :
    (ABI.padRightToWord b.toList).toByteArray = b ++ ⟨(List.replicate (32 - b.size) 0).toArray⟩ := by
  unfold ABI.padRightToWord ABI.zeroBytes
  rw [list_toByteArray_append, byteArray_toList_toByteArray, byteArray_toList_eq, Array.length_toList,
    show b.data.size = b.size from rfl,
    show ABI.paddedSize b.size - b.size = 32 - b.size from by unfold ABI.paddedSize; omega,
    list_toByteArray_eq]

/-- `Error(string)` for a message of at most 32 bytes: the tail's four `MSTORE`s lay the selector,
    the offset word `0x20`, the length word and the padded data at `0x80`, whatever the (at most
    128-byte) memory before. -/
theorem solcErrorStringPayload_eq {msg mem : ByteArray} {len word : UInt256}
    (hpos : 0 < msg.size) (hle : msg.size ≤ 32) (hmem : mem.size ≤ 128) (hlen : len.toNat = msg.size)
    (hword : UInt256.toByteArray word = msg ++ ⟨(List.replicate (32 - msg.size) 0).toArray⟩) :
    solcErrorStringPayload len word mem = errorStringData msg := by
  rw [show len = UInt256.ofNat msg.size from by rw [← hlen, u256_ofNat_toNat]]
  set P := mem ++ ffi.ByteArray.zeroes (128 - mem.size) with hP
  set S := UInt256.toByteArray solcErrorStringSelector with hS
  set W := UInt256.toByteArray (⟨32⟩ : UInt256) with hW
  set L := UInt256.toByteArray (UInt256.ofNat msg.size) with hL
  set D := UInt256.toByteArray word with hD
  have hPs : P.size = 128 := by rw [hP, ByteArray.size_append, ByteArray_zeroes_size]; omega
  have h0 : solcErrorStringMem0 mem = P ++ S := by
    unfold solcErrorStringMem0
    rw [toByteArray_write_eq _ _ _ hmem (lt_usize _ (by omega))]
  have h0s : (solcErrorStringMem0 mem).size = 160 := by
    rw [h0, ByteArray.size_append, hPs, hS, toByteArray_size]
  have h1 : solcErrorStringMem1 mem = P ++ S.extract 0 4 ++ W := by
    unfold solcErrorStringMem1
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [h0s]; omega), hW, toByteArray_extract_all,
      (ByteArray.extract_eq_empty_iff (b := solcErrorStringMem0 mem) (i := 132 + 32)
        (j := (solcErrorStringMem0 mem).size)).mpr (by rw [h0s]; omega),
      ByteArray.append_empty, h0, extract_append_span P S 0 132 (by omega) (by rw [hPs]; omega),
      byteArray_extract_self, hPs]
  have h1s : (solcErrorStringMem1 mem).size = 164 := by
    rw [h1, ByteArray.size_append, ByteArray.size_append, hPs, ByteArray.size_extract, hS, hW,
      toByteArray_size, toByteArray_size]
    omega
  have h2 : solcErrorStringMem2 (UInt256.ofNat msg.size) mem = solcErrorStringMem1 mem ++ L := by
    unfold solcErrorStringMem2
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [h1s]), hL, toByteArray_extract_all,
      (ByteArray.extract_eq_empty_iff (b := solcErrorStringMem1 mem) (i := 164 + 32)
        (j := (solcErrorStringMem1 mem).size)).mpr (by rw [h1s]; omega),
      ByteArray.append_empty, ← h1s, byteArray_extract_self]
  have h2s : (solcErrorStringMem2 (UInt256.ofNat msg.size) mem).size = 196 := by
    rw [h2, ByteArray.size_append, h1s, hL, toByteArray_size]
  have h3 : solcErrorStringMem3 (UInt256.ofNat msg.size) word mem =
      solcErrorStringMem2 (UInt256.ofNat msg.size) mem ++ D := by
    unfold solcErrorStringMem3
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [h2s]), hD, toByteArray_extract_all,
      (ByteArray.extract_eq_empty_iff (b := solcErrorStringMem2 (UInt256.ofNat msg.size) mem)
        (i := 196 + 32) (j := (solcErrorStringMem2 (UInt256.ofNat msg.size) mem).size)).mpr
        (by rw [h2s]; omega),
      ByteArray.append_empty, ← h2s, byteArray_extract_self]
  have h3s : (solcErrorStringMem3 (UInt256.ofNat msg.size) word mem).size = 228 := by
    rw [h3, ByteArray.size_append, h2s, hD, toByteArray_size]
  have hT : (S.extract 0 4 ++ (W ++ (L ++ D))).size = 100 := by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, hS, hW,
      hL, hD, toByteArray_size, toByteArray_size, toByteArray_size, toByteArray_size]
    omega
  unfold solcErrorStringPayload
  rw [readWithPadding_eq_extract' _ _ _ (by omega) (by omega) (by rw [h3s]), h3, h2, h1]
  simp only [ByteArray.append_assoc]
  rw [extract_append_right_window P _ _ _ (by rw [hPs]), hPs, Nat.sub_self, Nat.add_sub_cancel_left,
    ← hT, byteArray_extract_self]
  unfold errorStringData
  rw [encodeABIValues_string, Option.getD_some, list_toByteArray_append, list_toByteArray_append,
    natBytes_toByteArray, natBytes_toByteArray, padRightToWord_toByteArray msg hpos hle, ← hword,
    ← errorStringSelector_eq, hS, hW, hL, hD, show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from by decide]

/-! ## Event logs -/

/-- The log entry of an `(address indexed, address indexed, uint256)` event. -/
theorem mkLogEntry_addr_addr_u256 (this : EVM.Address) (ev : EventInfo) (a b : EVM.Address) (n : ℕ)
    {n1 n2 n3 : Option Ident}
    (hparams : ev.decl.params = [{ ty := .address false, indexed := true, name := n1 },
      { ty := .address false, indexed := true, name := n2 }, { ty := u256Ty, indexed := false, name := n3 }])
    (htys : ev.sig.paramTypes = [.elem .address, .elem .address, .elem (.int (.uint ⟨256, by decide⟩))])
    (hanon : ev.decl.anonymous = false) (hn : n < 2 ^ 256) :
    mkLogEntry this ev [.address a, .address b, .int n] =
      some { address := this,
             topics := #[hashWord ev.sigStr.toUTF8, UInt256.ofNat a.toNat, UInt256.ofNat b.toNat],
             data := UInt256.toByteArray (UInt256.ofNat n) } := by
  have hn' : n < EVM.twoPow 256 := hn
  have henc : ABI.encodeABIValues? [.elem (.int (.uint ⟨256, by decide⟩))] [.int n] =
      some (EVM.Word.toBytesBE (EVM.word n)) := by
    simp [ABI.encodeABIValues?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
      ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, hn']
  rw [show EVM.word n = UInt256.ofNat n from rfl] at henc
  simp [mkLogEntry, hparams, htys, hanon, topicOf, topicWordOf, ABI.valueToWord, henc, EVM.Word.ofNat,
    word_toBytesBE_toByteArray_eq_toByteArray]

/-- The log entry of an `(address, uint256)` event with no indexed argument (`LOG1`). -/
theorem mkLogEntry_addr_u256_plain (this : EVM.Address) (ev : EventInfo) (a : EVM.Address) (n : ℕ)
    {n1 n2 : Option Ident}
    (hparams : ev.decl.params = [{ ty := .address false, indexed := false, name := n1 },
      { ty := u256Ty, indexed := false, name := n2 }])
    (htys : ev.sig.paramTypes = [.elem .address, .elem (.int (.uint ⟨256, by decide⟩))])
    (hanon : ev.decl.anonymous = false) (hn : n < 2 ^ 256) :
    mkLogEntry this ev [.address a, .int n] =
      some { address := this, topics := #[hashWord ev.sigStr.toUTF8],
             data := UInt256.toByteArray (UInt256.ofNat a.toNat) ++ UInt256.toByteArray (UInt256.ofNat n) } := by
  have hn' : n < EVM.twoPow 256 := hn
  have henc : ABI.encodeABIValues? [.elem .address, .elem (.int (.uint ⟨256, by decide⟩))] [.address a, .int n] =
      some (EVM.Word.toBytesBE (EVM.word a.toNat) ++ EVM.Word.toBytesBE (EVM.word n)) := by
    simp [ABI.encodeABIValues?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
      ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, hn']
  rw [show EVM.word n = UInt256.ofNat n from rfl, show EVM.word a.toNat = UInt256.ofNat a.toNat from rfl] at henc
  simp [mkLogEntry, hparams, htys, hanon, henc, list_toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray]

/-- The log entry of an `(address indexed, address indexed)` event (`LOG3`, no data). -/
theorem mkLogEntry_addr_addr_indexed (this : EVM.Address) (ev : EventInfo) (a b : EVM.Address)
    {n1 n2 : Option Ident}
    (hparams : ev.decl.params = [{ ty := .address false, indexed := true, name := n1 },
      { ty := .address false, indexed := true, name := n2 }])
    (htys : ev.sig.paramTypes = [.elem .address, .elem .address])
    (hanon : ev.decl.anonymous = false) :
    mkLogEntry this ev [.address a, .address b] =
      some { address := this,
             topics := #[hashWord ev.sigStr.toUTF8, UInt256.ofNat a.toNat, UInt256.ofNat b.toNat],
             data := ByteArray.empty } := by
  simp [mkLogEntry, hparams, htys, hanon, topicOf, topicWordOf, ABI.valueToWord, EVM.Word.ofNat,
    ABI.encodeABIValues?, ABI.abiTupleHeadSize?, ABI.encodeABIValuesFrom?]

/-- The log entry of a `(bytes32 indexed, address indexed, address indexed)` event (`LOG4`, no data). -/
theorem mkLogEntry_bytes32_addr_addr_indexed (this : EVM.Address) (ev : EventInfo) (bs : List UInt8)
    (a b : EVM.Address) {n1 n2 n3 : Option Ident}
    (hparams : ev.decl.params = [{ ty := .fixedBytes ⟨31, by decide⟩, indexed := true, name := n1 },
      { ty := .address false, indexed := true, name := n2 }, { ty := .address false, indexed := true, name := n3 }])
    (htys : ev.sig.paramTypes = [.elem (.bytes ⟨31, by decide⟩), .elem .address, .elem .address])
    (hanon : ev.decl.anonymous = false) (hlen : bs.length = 32) :
    mkLogEntry this ev [.fixedBytes ⟨31, by decide⟩ bs, .address a, .address b] =
      some { address := this,
             topics := #[hashWord ev.sigStr.toUTF8, UInt256.ofNat (fromBytesBigEndian bs), UInt256.ofNat a.toNat,
               UInt256.ofNat b.toNat],
             data := ByteArray.empty } := by
  simp [mkLogEntry, hparams, htys, hanon, topicOf, topicWordOf, ABI.valueToWord, EVM.Word.ofNat, hlen,
    ABI.encodeABIValues?, ABI.abiTupleHeadSize?, ABI.encodeABIValuesFrom?]

/-! ## Events with value-type arguments -/

/-- A value-type event argument. -/
inductive LogVal
  | addr (a : EVM.Address)
  | u256 (n : ℕ)
  | bool (b : Bool)
  | bytes32 (bs : List UInt8)

structure LogArg where
  val : LogVal
  indexed : Bool
  name : Option Ident := none

namespace LogVal

def ty : LogVal → Ty
  | .addr _ => .address false
  | .u256 _ => u256Ty
  | .bool _ => .bool
  | .bytes32 _ => .fixedBytes ⟨31, by decide⟩

def abiTy : LogVal → ABI.ABIType
  | .addr _ => .elem .address
  | .u256 _ => .elem (.int (.uint ⟨256, by decide⟩))
  | .bool _ => .elem .bool
  | .bytes32 _ => .elem (.bytes ⟨31, by decide⟩)

def value : LogVal → ABI.ABIValue
  | .addr a => .address a
  | .u256 n => .int n
  | .bool b => .bool b
  | .bytes32 bs => .fixedBytes ⟨31, by decide⟩ bs

/-- The 32-byte word of the argument (its topic when indexed). -/
def word : LogVal → EVM.Word
  | .addr a => UInt256.ofNat a.toNat
  | .u256 n => UInt256.ofNat n
  | .bool b => b.toUInt256
  | .bytes32 bs => UInt256.ofNat (fromBytesBigEndian bs)

/-- The data bytes of the argument when not indexed. -/
def bytes : LogVal → List UInt8
  | .bytes32 bs => bs
  | v => v.word.toBytesBE

def wf : LogVal → Prop
  | .u256 n => n < 2 ^ 256
  | .bytes32 bs => bs.length = 32
  | _ => True

@[simp] theorem wf_addr (a : EVM.Address) : (LogVal.addr a).wf = True := rfl
@[simp] theorem wf_bool (b : Bool) : (LogVal.bool b).wf = True := rfl
@[simp] theorem wf_u256 (n : ℕ) : (LogVal.u256 n).wf = (n < 2 ^ 256) := rfl
@[simp] theorem wf_bytes32 (bs : List UInt8) : (LogVal.bytes32 bs).wf = (bs.length = 32) := rfl

theorem isDynamic_abiTy (v : LogVal) : ABI.isDynamicABIType v.abiTy = false := by
  cases v <;> rfl

theorem topicOf_eq (v : LogVal) (h : v.wf) : topicOf v.abiTy v.value = some v.word := by
  cases v with
  | addr a => simp [abiTy, value, word, topicOf, topicWordOf, ABI.valueToWord, EVM.Word.ofNat]
  | u256 n =>
    simp [abiTy, value, word, topicOf, topicWordOf, ABI.valueToWord, wordOfInt_nonneg]
    rfl
  | bool b => simp [abiTy, value, word, topicOf, topicWordOf, ABI.valueToWord]
  | bytes32 bs =>
    have hl : bs.length = 32 := h
    simp [abiTy, value, word, topicOf, topicWordOf, hl, EVM.Word.ofNat]

theorem encode_eq (v : LogVal) (h : v.wf) : ABI.encodeABIValue? v.abiTy v.value = some v.bytes := by
  cases v with
  | addr a =>
    simp [abiTy, value, bytes, word, ABI.encodeABIValue?, ABI.encodeABIWord?]
    rfl
  | u256 n =>
    have hn' : n < EVM.twoPow 256 := h
    simp [abiTy, value, bytes, word, ABI.encodeABIValue?, ABI.encodeABIWord?, hn']
    rfl
  | bool b => simp [abiTy, value, bytes, word, ABI.encodeABIValue?, ABI.encodeABIWord?]
  | bytes32 bs =>
    have hl : bs.length = 32 := h
    simp [abiTy, value, bytes, ABI.encodeABIValue?, hl, ABI.zeroBytes]

theorem staticSize_abiTy (v : LogVal) : ABI.staticABIEncodedSize? v.abiTy = some 32 := by
  cases v <;> simp [LogVal.abiTy, ABI.staticABIEncodedSize?]

end LogVal

def LogArg.param (x : LogArg) : EventParam := { ty := x.val.ty, indexed := x.indexed, name := x.name }

@[simp] theorem LogArg.param_indexed (x : LogArg) : x.param.indexed = x.indexed := rfl

theorem abiTupleHeadSize?_static : ∀ (xs : List LogArg),
    ABI.abiTupleHeadSize? (xs.map (·.val.abiTy)) = some (32 * xs.length)
  | [] => by simp [ABI.abiTupleHeadSize?]
  | x :: xs => by
    rw [List.map_cons, ABI.abiTupleHeadSize?, abiTupleHeadSize?_static xs, LogVal.isDynamic_abiTy,
      LogVal.staticSize_abiTy]
    simp [List.length_cons]
    ring

theorem encodeABIValuesFrom?_static : ∀ (xs : List LogArg) (hs : ℕ) (head tail : List UInt8),
    (∀ x ∈ xs, x.val.wf) →
    ABI.encodeABIValuesFrom? (xs.map (·.val.abiTy)) (xs.map (·.val.value)) hs head tail =
      some (head ++ xs.flatMap (·.val.bytes) ++ tail)
  | [], hs, head, tail, _ => by simp [ABI.encodeABIValuesFrom?]
  | x :: xs, hs, head, tail, hwf => by
    rw [List.map_cons, List.map_cons, ABI.encodeABIValuesFrom?, LogVal.encode_eq x.val (hwf x (by simp)),
      LogVal.isDynamic_abiTy]
    simp only [Opt.some_bind, Bool.false_eq_true, if_false]
    rw [encodeABIValuesFrom?_static xs hs _ tail (fun y hy => hwf y (by simp [hy]))]
    simp [List.append_assoc]

theorem encodeABIValues?_static (xs : List LogArg) (hwf : ∀ x ∈ xs, x.val.wf) :
    ABI.encodeABIValues? (xs.map (·.val.abiTy)) (xs.map (·.val.value)) = some (xs.flatMap (·.val.bytes)) := by
  rw [ABI.encodeABIValues?, abiTupleHeadSize?_static]
  simp [encodeABIValuesFrom?_static xs _ [] [] hwf]

theorem mapM_topicOf_static : ∀ (ys : List LogArg), (∀ x ∈ ys, x.val.wf) →
    List.mapM (fun x => topicOf x.1.2 x.2) (ys.map fun x => ((x.param, x.val.abiTy), x.val.value)) =
      some (ys.map (·.val.word))
  | [], _ => rfl
  | y :: ys, h => by
    simp only [List.map_cons, List.mapM_cons, LogVal.topicOf_eq y.val (h y (by simp)),
      mapM_topicOf_static ys (fun x hx => h x (by simp [hx]))]
    rfl

/-- The log entry of an event whose arguments are all value types (`address`, `uint256`, `bool`,
    `bytes32`), in any indexed pattern: `topics[0]` is the signature hash, then the indexed words;
    the data is the concatenation of the non-indexed words. -/
theorem mkLogEntry_static (this : EVM.Address) (ev : EventInfo) (xs : List LogArg)
    (hparams : ev.decl.params = xs.map LogArg.param) (htys : ev.sig.paramTypes = xs.map (·.val.abiTy))
    (hanon : ev.decl.anonymous = false) (hwf : ∀ x ∈ xs, x.val.wf) :
    mkLogEntry this ev (xs.map (·.val.value)) =
      some { address := this,
             topics := (hashWord ev.sigStr.toUTF8 :: (xs.filter (·.indexed)).map (·.val.word)).toArray,
             data := ((xs.filter (!·.indexed)).flatMap (·.val.bytes)).toByteArray } := by
  have hzip : ((xs.map LogArg.param).zip (xs.map (·.val.abiTy))).zip (xs.map (·.val.value)) =
      xs.map fun x => ((x.param, x.val.abiTy), x.val.value) := by
    rw [List.zip_map', List.zip_map']
  have hidx := mapM_topicOf_static (xs.filter (·.indexed)) (fun x hx => hwf x (List.mem_of_mem_filter hx))
  have hdata := encodeABIValues?_static (xs.filter (!·.indexed)) (fun x hx => hwf x (List.mem_of_mem_filter hx))
  simp only [mkLogEntry, hparams, htys, hanon, List.length_map, ne_eq, not_true_eq_false, or_self, if_false,
    hzip, List.filter_map, Function.comp_def, LogArg.param_indexed, List.map_map, Bool.false_eq_true]
  rw [hidx, hdata]
  simp

/-! ### The Solidity values of static event arguments and their `abiArgs` encoding -/
namespace LogVal
def solValue : LogVal → Value
  | .addr a => .address a
  | .u256 n => u256Val n
  | .bool b => .bool b
  | .bytes32 bs => .fixedBytes ⟨31, by decide⟩ bs
end LogVal

/-- One step of `abiArgs`: coerce to the parameter type, then `toAbi`. -/
def abiArgStep (cfg : Config) (env : TypeEnv) (accm : List ABI.ABIValue × Machine) (tv : Ty × Value) :
    Op (List ABI.ABIValue × Machine) := do
  let r ← coerce cfg env accm.2 tv.2 tv.1 (some .memory)
  match toAbi r.2.heap fuelDefault r.1 with
  | some sv => pure (accm.1 ++ [sv], r.2)
  | _ => Op.stuck

theorem abiArgs_eq_foldlM (cfg : Config) (env : TypeEnv) (m : Machine) (tys : List Ty) (vs : List Value)
    (hlen : tys.length = vs.length) :
    abiArgs cfg env m tys vs = (tys.zip vs).foldlM (abiArgStep cfg env) ([], m) := by
  simp only [abiArgs, hlen, ne_eq, not_true_eq_false, if_false]
  rfl

theorem abiArgStep_static (cfg : Config) (env : TypeEnv) (acc : List ABI.ABIValue) (m : Machine) (v : LogVal) :
    abiArgStep cfg env (acc, m) (v.ty, v.solValue) = some (.ok (acc ++ [v.value], m)) := by
  cases v <;> simp [abiArgStep, LogVal.ty, LogVal.solValue, LogVal.value, coerce, fuelDefault]

theorem abiArgs_static_fold (cfg : Config) (env : TypeEnv) : ∀ (xs : List LogArg) (acc : List ABI.ABIValue) (m : Machine),
    ((xs.map (·.val.ty)).zip (xs.map (·.val.solValue))).foldlM (abiArgStep cfg env) (acc, m) =
      some (.ok (acc ++ xs.map (·.val.value), m))
  | [], acc, m => by simp
  | x :: xs, acc, m => by
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.foldlM_cons, abiArgStep_static, Op.bind_ok,
      abiArgs_static_fold cfg env xs (acc ++ [x.val.value]) m, List.map_cons, List.append_assoc, List.singleton_append]

theorem eventArgFits_static (env : TypeEnv) (hp : Heap) (v : LogVal) :
    eventArgFits env hp v.solValue v.ty = true := by
  cases v <;> simp [eventArgFits, LogVal.ty, LogVal.solValue, implicitConv]

/-- Static arguments fit the event they were built for (overload resolution). -/
theorem eventFits_static (env : TypeEnv) (hp : Heap) (ei : EventInfo) (xs : List LogArg)
    (hparams : ei.decl.params = xs.map LogArg.param) :
    eventFits env hp ei (xs.map (·.val.solValue)) = true := by
  simp only [eventFits, hparams, List.length_map, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro pv hpv
  rw [List.zip_map'] at hpv
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hpv
  exact eventArgFits_static env hp x.val

theorem abiArgs_static (cfg : Config) (env : TypeEnv) (m : Machine) (xs : List LogArg) :
    abiArgs cfg env m (xs.map (·.val.ty)) (xs.map (·.val.solValue)) = some (.ok (xs.map (·.val.value), m)) := by
  rw [abiArgs_eq_foldlM _ _ _ _ _ (by simp), abiArgs_static_fold, List.nil_append]

/-! ## ABI tuple encoding from the per-element encodings (static and dynamic) -/

/-- Head and tail of an ABI tuple encoding: a dynamic element puts its offset in the head and its
    encoding in the tail, a static one its encoding in the head. -/
def abiHeadTail (hs : ℕ) : List (Bool × List UInt8) → List UInt8 → List UInt8 → List UInt8 × List UInt8
  | [], head, tail => (head, tail)
  | (true, enc) :: rest, head, tail => abiHeadTail hs rest (head ++ ABI.natBytes (hs + tail.length)) (tail ++ enc)
  | (false, enc) :: rest, head, tail => abiHeadTail hs rest (head ++ enc) tail

theorem encodeABIValuesFrom?_of_encs :
    ∀ (xs : List (ABI.ABIType × ABI.ABIValue × List UInt8)) (hs : ℕ) (head tail : List UInt8),
    (∀ x ∈ xs, ABI.encodeABIValue? x.1 x.2.1 = some x.2.2) →
    ABI.encodeABIValuesFrom? (xs.map (·.1)) (xs.map (·.2.1)) hs head tail =
      some ((abiHeadTail hs (xs.map fun x => (ABI.isDynamicABIType x.1, x.2.2)) head tail).1 ++
        (abiHeadTail hs (xs.map fun x => (ABI.isDynamicABIType x.1, x.2.2)) head tail).2)
  | [], hs, head, tail, _ => by simp [ABI.encodeABIValuesFrom?, abiHeadTail]
  | x :: xs, hs, head, tail, h => by
    rw [List.map_cons, List.map_cons, ABI.encodeABIValuesFrom?, h x (by simp)]
    simp only [Opt.some_bind, List.map_cons]
    cases hd : ABI.isDynamicABIType x.1
    · simp only [Bool.false_eq_true, if_false, abiHeadTail]
      exact encodeABIValuesFrom?_of_encs xs hs _ tail (fun y hy => h y (by simp [hy]))
    · simp only [if_true, abiHeadTail]
      exact encodeABIValuesFrom?_of_encs xs hs _ _ (fun y hy => h y (by simp [hy]))

/-- `encodeABIValues?` from the per-element encodings and the tuple head size. -/
theorem encodeABIValues?_of_encs (xs : List (ABI.ABIType × ABI.ABIValue × List UInt8)) (hs : ℕ)
    (hhs : ABI.abiTupleHeadSize? (xs.map (·.1)) = some hs)
    (h : ∀ x ∈ xs, ABI.encodeABIValue? x.1 x.2.1 = some x.2.2) :
    ABI.encodeABIValues? (xs.map (·.1)) (xs.map (·.2.1)) =
      some ((abiHeadTail hs (xs.map fun x => (ABI.isDynamicABIType x.1, x.2.2)) [] []).1 ++
        (abiHeadTail hs (xs.map fun x => (ABI.isDynamicABIType x.1, x.2.2)) [] []).2) := by
  rw [ABI.encodeABIValues?, hhs]
  simp only [Opt.some_bind]
  exact encodeABIValuesFrom?_of_encs xs hs [] [] h

@[simp] theorem encodeABIValue?_string (b : ByteArray) :
    ABI.encodeABIValue? .string (.bytes b) = some (ABI.natBytes b.size ++ ABI.padRightToWord b.toList) := by
  simp [ABI.encodeABIValue?]
@[simp] theorem encodeABIValue?_bytes (b : ByteArray) :
    ABI.encodeABIValue? .bytes (.bytes b) = some (ABI.natBytes b.size ++ ABI.padRightToWord b.toList) := by
  simp [ABI.encodeABIValue?]
@[simp] theorem topicOf_string (b : ByteArray) : topicOf .string (.bytes b) = some (hashWord b) := rfl
@[simp] theorem topicOf_bytes (b : ByteArray) : topicOf .bytes (.bytes b) = some (hashWord b) := rfl

/-- `string memory s` as an event or call argument. -/
theorem abiArgs_memString {cfg : Config} {env : TypeEnv} {m : Machine} {id : ℕ} {b : ByteArray}
    (hget : m.heap.get? id = some (.bytes true b)) :
    abiArgs cfg env m [.string] [.memRef id] = some (.ok ([.bytes b], m)) := by
  simp [abiArgs, coerce, implicitConv, fuelDefault, toAbi_memBytes 1023 hget]

theorem abiArgs_memBytes {cfg : Config} {env : TypeEnv} {m : Machine} {id : ℕ} {b : ByteArray}
    (hget : m.heap.get? id = some (.bytes false b)) :
    abiArgs cfg env m [.bytes] [.memRef id] = some (.ok ([.bytes b], m)) := by
  simp [abiArgs, coerce, implicitConv, fuelDefault, toAbi_memBytes 1023 hget]

/-- The log entry of an event with one non-indexed `string` argument. -/
theorem mkLogEntry_string (this : EVM.Address) (ev : EventInfo) (b : ByteArray) {n1 : Option Ident}
    (hparams : ev.decl.params = [{ ty := .string, indexed := false, name := n1 }])
    (htys : ev.sig.paramTypes = [.string]) (hanon : ev.decl.anonymous = false) :
    mkLogEntry this ev [.bytes b] =
      some { address := this, topics := #[hashWord ev.sigStr.toUTF8],
             data := (ABI.natBytes 32 ++ (ABI.natBytes b.size ++ ABI.padRightToWord b.toList)).toByteArray } := by
  simp [mkLogEntry, hparams, htys, hanon, encodeABIValues_string]

/-- The log entry of an `(address indexed, string)` event. -/
theorem mkLogEntry_addr_indexed_string (this : EVM.Address) (ev : EventInfo) (a : EVM.Address) (b : ByteArray)
    {n1 n2 : Option Ident}
    (hparams : ev.decl.params = [{ ty := .address false, indexed := true, name := n1 },
      { ty := .string, indexed := false, name := n2 }])
    (htys : ev.sig.paramTypes = [.elem .address, .string]) (hanon : ev.decl.anonymous = false) :
    mkLogEntry this ev [.address a, .bytes b] =
      some { address := this, topics := #[hashWord ev.sigStr.toUTF8, UInt256.ofNat a.toNat],
             data := (ABI.natBytes 32 ++ (ABI.natBytes b.size ++ ABI.padRightToWord b.toList)).toByteArray } := by
  simp [mkLogEntry, hparams, htys, hanon, topicOf, topicWordOf, ABI.valueToWord, EVM.Word.ofNat, encodeABIValues_string]

/-! ## Arrays of static elements in the ABI (events, `abi.encode`) -/

theorem encodeABIStaticArrayElems?_of_encs (t : ABI.ElemType) :
    ∀ (xs : List (ABI.ABIValue × List UInt8)), (∀ x ∈ xs, ABI.encodeABIValue? (.elem t) x.1 = some x.2) →
    ABI.encodeABIStaticArrayElems? (.elem t) (xs.map (·.1)) = some (xs.flatMap (·.2))
  | [], _ => by simp [ABI.encodeABIStaticArrayElems?]
  | x :: xs, h => by
    rw [List.map_cons, ABI.encodeABIStaticArrayElems?, h x (by simp),
      encodeABIStaticArrayElems?_of_encs t xs (fun y hy => h y (by simp [hy]))]
    simp

theorem encodeABIArrayElems?_static (t : ABI.ElemType) (xs : List (ABI.ABIValue × List UInt8))
    (h : ∀ x ∈ xs, ABI.encodeABIValue? (.elem t) x.1 = some x.2) :
    ABI.encodeABIArrayElems? (.elem t) (xs.map (·.1)) = some (xs.flatMap (·.2)) := by
  rw [ABI.encodeABIArrayElems?]
  simp only [ABI.isDynamicABIType, Bool.false_eq_true, if_false]
  exact encodeABIStaticArrayElems?_of_encs t xs h

/-- `T[]` with static `T`: the length word, then the elements. -/
theorem encodeABIValue?_dynArray_static (t : ABI.ElemType) (xs : List (ABI.ABIValue × List UInt8))
    (h : ∀ x ∈ xs, ABI.encodeABIValue? (.elem t) x.1 = some x.2) :
    ABI.encodeABIValue? (.dynamicArray (.elem t)) (.array (xs.map (·.1))) =
      some (ABI.natBytes xs.length ++ xs.flatMap (·.2)) := by
  rw [ABI.encodeABIValue?, encodeABIArrayElems?_static t xs h]
  simp

/-- `T[n]` with static `T`: just the elements. -/
theorem encodeABIValue?_array_static (t : ABI.ElemType) (n : ℕ) (xs : List (ABI.ABIValue × List UInt8))
    (hn : xs.length = n) (h : ∀ x ∈ xs, ABI.encodeABIValue? (.elem t) x.1 = some x.2) :
    ABI.encodeABIValue? (.array (.elem t) n) (.array (xs.map (·.1))) = some (xs.flatMap (·.2)) := by
  rw [ABI.encodeABIValue?]
  simp only [List.length_map, hn, if_true]
  exact encodeABIArrayElems?_static t xs h

/-- The topic of an indexed `T[]` argument: the hash of the in-place element encoding. -/
theorem topicOf_dynArray_static (t : ABI.ElemType) (xs : List (ABI.ABIValue × List UInt8))
    (h : ∀ x ∈ xs, ABI.encodeABIValue? (.elem t) x.1 = some x.2) :
    topicOf (.dynamicArray (.elem t)) (.array (xs.map (·.1))) = some (hashWord (xs.flatMap (·.2)).toByteArray) := by
  simp [topicOf, encodeABIArrayElems?_static t xs h]

theorem encodeABIValue?_u256 (n : ℕ) (hn : n < 2 ^ 256) :
    ABI.encodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩))) (.int n) = some (EVM.Word.toBytesBE (UInt256.ofNat n)) := by
  have hn' : n < EVM.twoPow 256 := hn
  simp [ABI.encodeABIValue?, ABI.encodeABIWord?, hn']
  rfl

theorem encodeABIValue?_address (a : EVM.Address) :
    ABI.encodeABIValue? (.elem .address) (.address a) = some (EVM.Word.toBytesBE (UInt256.ofNat a.toNat)) := by
  simp [ABI.encodeABIValue?, ABI.encodeABIWord?]
  rfl

theorem mapM_toAbi_u256 (h : Heap) (fuel : ℕ) : ∀ (ns : List ℕ),
    (ns.map u256Val).mapM (toAbi h (fuel + 1)) = some (ns.map fun (n : ℕ) => ABI.ABIValue.int n)
  | [] => rfl
  | n :: ns => by simp [List.mapM_cons, toAbi_uint, mapM_toAbi_u256 h fuel ns]

/-- A memory `uint256[]` as an ABI argument. -/
theorem toAbi_memArray_u256 {h : Heap} {id : ℕ} {ety : Ty} {ns : List ℕ} (fuel : ℕ)
    (hget : h.get? id = some (.array ety (ns.map u256Val))) :
    toAbi h (fuel + 2) (.memRef id) = some (.array (ns.map fun (n : ℕ) => ABI.ABIValue.int n)) := by
  rw [toAbi]
  simp only [hget]
  rw [mapM_toAbi_u256 h fuel ns]
  rfl

theorem abiArgs_memArray_u256 {cfg : Config} {env : TypeEnv} {m : Machine} {id : ℕ} {ety : Ty} {ns : List ℕ}
    (hget : m.heap.get? id = some (.array ety (ns.map u256Val))) :
    abiArgs cfg env m [.dynArray u256Ty] [.memRef id] = some (.ok ([.array (ns.map fun (n : ℕ) => ABI.ABIValue.int n)], m)) := by
  simp [abiArgs, coerce, implicitConv, fuelDefault, toAbi_memArray_u256 1022 hget]

theorem encodeABIStaticArrayElems?_u256 : ∀ (ns : List ℕ), (∀ n ∈ ns, n < 2 ^ 256) →
    ABI.encodeABIStaticArrayElems? (.elem (.int (.uint ⟨256, by decide⟩))) (ns.map fun (n : ℕ) => ABI.ABIValue.int n) =
      some (ns.flatMap fun (n : ℕ) => EVM.Word.toBytesBE (UInt256.ofNat n))
  | [], _ => by simp [ABI.encodeABIStaticArrayElems?]
  | n :: ns, h => by
    rw [List.map_cons, ABI.encodeABIStaticArrayElems?, encodeABIValue?_u256 n (h n (by simp)),
      encodeABIStaticArrayElems?_u256 ns (fun x hx => h x (by simp [hx]))]
    simp

/-- `uint256[]`: the length word, then the words. -/
theorem encodeABIValue?_dynArray_u256 (ns : List ℕ) (hns : ∀ n ∈ ns, n < 2 ^ 256) :
    ABI.encodeABIValue? (.dynamicArray (.elem (.int (.uint ⟨256, by decide⟩)))) (.array (ns.map fun (n : ℕ) => ABI.ABIValue.int n)) =
      some (ABI.natBytes ns.length ++ ns.flatMap fun (n : ℕ) => EVM.Word.toBytesBE (UInt256.ofNat n)) := by
  rw [ABI.encodeABIValue?, ABI.encodeABIArrayElems?]
  simp [ABI.isDynamicABIType, encodeABIStaticArrayElems?_u256 ns hns]

/-- The log entry of an event with one non-indexed `uint256[]` argument. -/
theorem mkLogEntry_u256Array (this : EVM.Address) (ev : EventInfo) (ns : List ℕ) {n1 : Option Ident}
    (hparams : ev.decl.params = [{ ty := .dynArray u256Ty, indexed := false, name := n1 }])
    (htys : ev.sig.paramTypes = [.dynamicArray (.elem (.int (.uint ⟨256, by decide⟩)))])
    (hanon : ev.decl.anonymous = false) (hns : ∀ n ∈ ns, n < 2 ^ 256) :
    mkLogEntry this ev [.array (ns.map fun (n : ℕ) => ABI.ABIValue.int n)] =
      some { address := this, topics := #[hashWord ev.sigStr.toUTF8],
             data := (ABI.natBytes 32 ++ (ABI.natBytes ns.length ++
               ns.flatMap fun (n : ℕ) => EVM.Word.toBytesBE (UInt256.ofNat n))).toByteArray } := by
  have hall : ABI.encodeABIValues? [.dynamicArray (.elem (.int (.uint ⟨256, by decide⟩)))]
      [.array (ns.map fun (n : ℕ) => ABI.ABIValue.int n)] =
      some (ABI.natBytes 32 ++ (ABI.natBytes ns.length ++ ns.flatMap fun (n : ℕ) => EVM.Word.toBytesBE (UInt256.ofNat n))) := by
    rw [ABI.encodeABIValues?]
    simp [ABI.abiTupleHeadSize?, ABI.encodeABIValuesFrom?, ABI.isDynamicABIType, encodeABIValue?_dynArray_u256 ns hns]
  simp [mkLogEntry, hparams, htys, hanon, hall]

/-! ## Dispatch -/

theorem selectorDispatch_short {fc : FlatContract} {cd : ByteArray} (h : cd.size < 4) :
    selectorDispatch fc cd = none := by
  simp [selectorDispatch, h]

theorem selectorDispatch_of_size {fc : FlatContract} {cd : ByteArray} (h : 4 ≤ cd.size) :
    selectorDispatch fc cd = fc.entries.find? fun e => selectorOf e.sigStr == cd.extract 0 4 := by
  simp [selectorDispatch, Nat.not_lt.mpr h]

theorem dispatches_eq_false {fc : FlatContract} {cd : ByteArray} (hsel : selectorDispatch fc cd = none)
    (hrecv : fc.receive? = none ∨ cd.size ≠ 0) (hfb : fc.fallback? = none) : dispatches fc cd = false := by
  simp only [dispatches, hsel, hfb, Option.isSome_none, Bool.false_or, Bool.or_false]
  rcases hrecv with h | h <;> simp [h]

/-- Skip the first `n` selector arms, none of which matches. -/
theorem Run.dispatchNoMatch {code : ByteArray} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {w : World} {selWord : UInt256} {rest : List UInt256} :
    ∀ (n : ℕ) {start : UInt256} {k C : ℕ}
      (_ : Run code s0 ⟨start, selWord :: rest, mem, aw, rdata, w⟩ k C)
      (_ : ∀ j, j < n → armWellFormed code (nthArmPc code start j))
      (_ : ∀ j, j < n → UInt256.eq (armSelNat code (nthArmPc code start j)) selWord = ⟨0⟩)
      (_ : rest.length + 3 ≤ 1024),
      ∃ k' C', Run code s0 ⟨nthArmPc code start n, selWord :: rest, mem, aw, rdata, w⟩ k' C' := by
  intro n
  induction n with
  | zero => intro start k C h _ _ _; exact ⟨k, C, h⟩
  | succ n ih =>
    intro start k C h hwf heq0 hov
    exact ih (h.selectorArmNotTakenAuto (hwf 0 (Nat.succ_pos n)) (heq0 0 (Nat.succ_pos n)) hov)
      (fun j hj => hwf (j + 1) (by omega)) (fun j hj => heq0 (j + 1) (by omega)) hov

/-- `callvalue ≠ 0` on a non-payable dispatcher: the guard's `PUSH0; PUSH0; REVERT`. -/
theorem Run.solcDispatchNonPayableRevert {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    {firstArmPc : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩)
    (hprefix : solcDispatchPrefixWellFormed code firstArmPc)
    (hr0 : decode code (solcGuardJumpiPc code + ⟨1⟩) = some (.PUSH0, .none))
    (hr1 : decode code (solcGuardJumpiPc code + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (solcGuardJumpiPc code + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    Reverted code (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨hd0, hd2, hd4, hd5, hd6, hd7, hguardOp, hguardPush, hguardJumpi, _⟩ := hprefix
  exact Run.solcGuardCallvalueNonzeroRevert (ctgt := solcGuardTgt code) (opC := solcGuardTgtOp code)
    (wC := solcGuardTgtWidth code)
    (Run.solcGuardPrologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
      hcode hd0 hd2 hd4 hd5 hd6 hd7)
    hwv hguardOp hguardPush hguardJumpi hr0 hr1 hr2

/-- Calldata shorter than a selector: the dispatcher's short-calldata `PUSH0; PUSH0; REVERT`. -/
theorem Run.solcDispatchShortRevert {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    {firstArmPc : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩) (hshort : I.calldata.size < 4)
    (hprefix : solcDispatchPrefixWellFormed code firstArmPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hrevJd : decode code (solcCalldataRevertTgt code) = some (.JUMPDEST, .none))
    (hrevD : (D_J code 0).contains (solcCalldataRevertTgt code) = true)
    (hr0 : decode code (solcCalldataRevertTgt code + ⟨1⟩) = some (.PUSH0, .none))
    (hr1 : decode code (solcCalldataRevertTgt code + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (solcCalldataRevertTgt code + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    Reverted code (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨hd0, hd2, hd4, hd5, hd6, hd7, hguardOp, hguardPush, hguardJumpi, hguardDest, hguardPop,
    hcdPush4, hcdSize, hcdLt, hcdOp, hcdPushRevert, hcdJumpi, _⟩ := hprefix
  have h0 := Run.solcGuardPrologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hd0 hd2 hd4 hd5 hd6 hd7
  obtain ⟨_, _, h1⟩ := Run.solcGuardCallvalueZero (ctgt := solcGuardTgt code) (opC := solcGuardTgtOp code)
    (wC := solcGuardTgtWidth code) h0 hwv hguardOp hguardPush hguardJumpi hguardDest hguardPop hguardJd
  exact Run.solcCalldataShortRevert (rtgt := solcCalldataRevertTgt code) (opR := solcCalldataRevertTgtOp code)
    (wR := solcCalldataRevertTgtWidth code) h1 hshort hcdPush4 hcdSize hcdLt hcdOp hcdPushRevert hcdJumpi
    hrevJd hrevD hr0 hr1 hr2

/-- No selector arm matches: fall through the `n` arms into `JUMPDEST; PUSH0; PUSH0; REVERT`. -/
theorem Run.solcDispatchNoMatchRevert {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    {firstArmPc : UInt256} {n : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code firstArmPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hwf : ∀ j, j < n → armWellFormed code (nthArmPc code firstArmPc j))
    (heq0 : ∀ j, j < n →
      UInt256.eq (armSelNat code (nthArmPc code firstArmPc j)) (solcSelectorWord I) = ⟨0⟩)
    (hjd : decode code (nthArmPc code firstArmPc n) = some (.JUMPDEST, .none))
    (hr0 : decode code (nthArmPc code firstArmPc n + ⟨1⟩) = some (.PUSH0, .none))
    (hr1 : decode code (nthArmPc code firstArmPc n + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (nthArmPc code firstArmPc n + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    Reverted code (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := Run.solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix hguardJd
  obtain ⟨_, _, h'⟩ := Run.dispatchNoMatch n h hwf heq0 (by simp)
  exact (h'.jumpdest hjd (by simp)).revertStub hr0 hr1 hr2 (by simp)

/-- `decodeArgs` is the calldata decoder on the function's signature. -/
theorem decodeArgs_eq {cfg : Config} {env : TypeEnv} {d : FnDecl} {cd : ByteArray} {sig : ABI.Signature}
    (hsig : sigOf env d.name (d.params.map (·.ty)) = some sig) :
    decodeArgs cfg env d cd = ABI.decodeCalldataValues? sig.paramTypes cd cfg.abiDecodeMode := by
  unfold decodeArgs
  rw [hsig, Opt.some_bind]

theorem payableOrNoValue_of_zero {d : FnDecl} {I : ExecutionEnv} (h : I.weiValue = ⟨0⟩) : payableOrNoValue d I :=
  Or.inr h

theorem ctorPayable_iff_of_nonpayable {fc : FlatContract} {I : ExecutionEnv} {f : FnDef}
    (htop : topCtor? fc = some f) (hne : f.decl.mutability ≠ .payable) : ctorPayable fc I ↔ I.weiValue = ⟨0⟩ := by
  unfold ctorPayable
  rw [htop]
  exact ⟨fun h => h.resolve_left hne, Or.inr⟩

theorem ctorPayable_iff_of_none {fc : FlatContract} {I : ExecutionEnv} (htop : topCtor? fc = none) :
    ctorPayable fc I ↔ I.weiValue = ⟨0⟩ := by
  unfold ctorPayable
  rw [htop]

theorem ctorPayable_of_payable {fc : FlatContract} {I : ExecutionEnv} {f : FnDef}
    (htop : topCtor? fc = some f) (hp : f.decl.mutability = .payable) : ctorPayable fc I := by
  unfold ctorPayable
  rw [htop]
  exact Or.inl hp

@[simp] theorem constCode_apply (code : ByteArray) (imms : Store) : constCode code imms = some code := rfl

/-- The initcode's empty revert when construction is not payable and value was sent. -/
theorem Reverted.specCtorNonPayable {cfg fc args cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code : ByteArray}
    {runtimeCodeOf : Store → Option ByteArray}
    (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty)
    (hnp : ¬ ctorPayable fc I) :
    constructorEquivalenceFor cfg fc args cA gh bl σ_evm σ_spec σ₀ g A I runtimeCodeOf :=
  Reverted.specCtorRevert default hcode h (solidityCtorExec.nonPayable hnp)

/-- A returned run of the `receive` function. -/
theorem Returned.specReceive {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code out : ByteArray}
    {w : World} {m' : Machine} {fid : FnId} {fn : FnDef} {rets : List Value}
    (o : Oracle) (hcode : I.code = code)
    (h : Returned code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) w out)
    (hcd : I.calldata.size = 0) (hrecv : fc.receive? = some fid) (hfn : fc.fns[fid]? = some fn)
    (hcall : CallFn cfg o fc (rootFrame fc) (initMachine cA gh bl σ_spec σ₀ g A I) fn [] (.ok rets m'))
    (hw : WorldEquiv w m') (henc : returnDataEquiv out [] (.abi [])) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Returned.specExecutionW o hcode h (solidityExec.receive hcd hrecv hfn hcall) hw henc

/-- A reverted run of the `receive` function. -/
theorem Reverted.specReceiveRevert {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code d : ByteArray}
    {fid : FnId} {fn : FnDef}
    (o : Oracle) (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) d)
    (hcd : I.calldata.size = 0) (hrecv : fc.receive? = some fid) (hfn : fc.fns[fid]? = some fn)
    (hcall : CallFn cfg o fc (rootFrame fc) (initMachine cA gh bl σ_spec σ₀ g A I) fn [] (.reverted d)) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Reverted.specRevert o hcode h (solidityExec.receiveReverted hcd hrecv hfn hcall)

/-- A returned run of the `fallback` function. -/
theorem Returned.specFallback {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code out : ByteArray}
    {w : World} {m' : Machine} {fid : FnId} {fn : FnDef} {vs rets : List Value} {h0 : Heap}
    {abiOut : List ABI.ABIValue}
    (o : Oracle) (hcode : I.code = code)
    (h : Returned code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) w out)
    (hsel : selectorDispatch fc I.calldata = none) (hrecv : fc.receive? = none ∨ I.calldata.size ≠ 0)
    (hfb : fc.fallback? = some fid) (hfn : fc.fns[fid]? = some fn) (hpay : payableOrNoValue fn.decl I)
    (hargs : fallbackArgs fn.decl I.calldata {} = some (vs, h0))
    (hcall : CallFn cfg o fc (rootFrame fc) (initMachine cA gh bl σ_spec σ₀ g A I h0) fn vs (.ok rets m'))
    (hout : rets.mapM (toAbi m'.heap fuelDefault) = some abiOut)
    (hw : WorldEquiv w m') (henc : returnDataEquiv out abiOut (fallbackConvention fn.decl)) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Returned.specExecutionW o hcode h (solidityExec.fallback hsel hrecv hfb hfn hpay hargs hcall hout) hw henc

/-- A reverted run of the `fallback` function. -/
theorem Reverted.specFallbackRevert {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code d : ByteArray}
    {fid : FnId} {fn : FnDef} {vs : List Value} {h0 : Heap}
    (o : Oracle) (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) d)
    (hsel : selectorDispatch fc I.calldata = none) (hrecv : fc.receive? = none ∨ I.calldata.size ≠ 0)
    (hfb : fc.fallback? = some fid) (hfn : fc.fns[fid]? = some fn) (hpay : payableOrNoValue fn.decl I)
    (hargs : fallbackArgs fn.decl I.calldata {} = some (vs, h0))
    (hcall : CallFn cfg o fc (rootFrame fc) (initMachine cA gh bl σ_spec σ₀ g A I h0) fn vs (.reverted d)) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Reverted.specRevert o hcode h (solidityExec.fallbackReverted hsel hrecv hfb hfn hpay hargs hcall)

/-- The spec rejects a non-payable call carrying value. -/
theorem Reverted.specNonPayable {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code : ByteArray}
    {e : DispatchEntry} {fn : FnDef} {retTys : List ABI.ABIType}
    (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty)
    (he : selectorDispatch fc I.calldata = some e) (hfn : fc.fns[e.fn]? = some fn)
    (hne : fn.decl.mutability ≠ .payable) (hwv : I.weiValue ≠ ⟨0⟩)
    (hret : returnAbiTys fc.types fn.decl = some retTys) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Reverted.specRevert default hcode h (solidityExec.nonPayable he hfn hne hwv hret)

/-- The spec rejects value sent to a non-payable `fallback`. -/
theorem Reverted.specFallbackNonPayable {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code : ByteArray}
    {fid : FnId} {fn : FnDef}
    (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty)
    (hsel : selectorDispatch fc I.calldata = none) (hrecv : fc.receive? = none ∨ I.calldata.size ≠ 0)
    (hfb : fc.fallback? = some fid) (hfn : fc.fns[fid]? = some fn)
    (hne : fn.decl.mutability ≠ .payable) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Reverted.specRevert default hcode h (solidityExec.fallbackNonPayable hsel hrecv hfb hfn hne hwv)

/-- No entry point accepts the calldata (no selector match, no applicable `receive`, no `fallback`). -/
theorem Reverted.specUndispatched {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (h : Reverted code (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty)
    (hsel : selectorDispatch fc I.calldata = none) (hrecv : fc.receive? = none ∨ I.calldata.size ≠ 0)
    (hfb : fc.fallback? = none) :
    runtimeEquivalenceFor cfg fc cA gh bl σ_evm σ_spec σ₀ g A I :=
  Reverted.specNoDispatch hcode h (dispatches_eq_false hsel hrecv hfb)

end Solidity
