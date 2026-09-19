import Solidity.Examples.ERC20.Transfer

/-!
# ERC20 — the constructor refines its Solidity body (core relation)

Against the pinned hand-written initcode (`erc20Initcode`): accounts and returned runtime code
only, since that initcode does not emit the `Transfer` log the Solidity constructor emits.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

/-! ## Static facts -/

theorem erc20Flat_topCtor : topCtor? erc20Flat = some fnCtor := rfl
theorem erc20Flat_immZero : immZero erc20Flat = some ∅ := rfl
theorem erc20Flat_initializers : initializers erc20Flat = [] := rfl

/-- The Solidity deployment scheme coincides with the Sol⁻ one. -/
theorem erc20SolDeployment (args : List Solm.Value) :
    erc20Cfg.selfDeployment erc20Initcode args = erc20Config.selfDeployment erc20Initcode args := rfl

theorem ofAbi_u256_int (env : TypeEnv) (fuel : Nat) (i : Int) (h : Heap) (h0 : 0 ≤ i) (hlt : i < 2 ^ 256) :
    ofAbi env (fuel + 1) u256 (.int i) h = some (u256Val i.toNat, h) := by
  simp only [ofAbi]
  simp [scalarOfSolm, h0]
  omega

/-- `ofAbi_u256` with the argument in cast form (the form `simp` produces). -/
@[simp] theorem ofAbi_u256' (env : TypeEnv) (fuel : Nat) (w : UInt256) (h : Heap) :
    ofAbi env (fuel + 1) u256 (.int (w.toNat : Int)) h = some (u256Val w.toNat, h) := by
  simpa using ofAbi_u256 env fuel w h

theorem ctorPayable_erc20 {I : ExecutionEnv} : ctorPayable erc20Flat I ↔ I.weiValue = ⟨0⟩ := by
  unfold ctorPayable
  rw [erc20Flat_topCtor]
  simp [fnCtor]

/-! ## The body derivation -/

def ctorStmts : Block :=
  [ .exprStmt (.assign .assign (.index (.ident "balanceOf") msgSender) (.ident "initialSupply")),
    .exprStmt (.assign .assign (.ident "totalSupply") (.ident "initialSupply")),
    .emit (.ident "Transfer") (.positional
      [ .call (.typeExpr addrTy) [] (.positional [.lit (.number 0 none)]), msgSender, .ident "initialSupply" ]) ]

/-- The parameter frame (base-constructor arguments are evaluated in it). -/
def ctorFrameP (w : UInt256) : Frame :=
  ({ here := "ERC20", locals := ∅, retVars := [] } : Frame).bind "initialSupply" u256 (some .memory) (u256Val w.toNat)

/-- The constructor's own frame: the parameter over the (empty) immutables of the parameter frame. -/
def ctorFr (w : UInt256) : Frame :=
  bodyFrame (({ here := "ERC20", locals := immStore (ctorFrameP w), retVars := [] } : Frame).bind "initialSupply" u256
    (some .memory) (u256Val w.toNat)) ctorStmts

theorem ctorParam (m : Machine) (w : UInt256) :
    ctorParamFrame erc20Cfg erc20Flat [u256Val w.toNat] m ∅ = some (.ok (ctorFrameP w, m)) := by
  simp [ctorParamFrame, erc20Flat_topCtor, enterFn, declare, coerce, fnCtor, fuelDefault, ctorFrameP]
  try rfl

theorem ctorEnter (m : Machine) (w : UInt256) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnCtor.decl [u256Val w.toNat] m (immStore (ctorFrameP w)) =
      some (.ok ({ ctorFr w with chain := [], body := [] }, m)) := by
  simp [enterFn, declare, coerce, fnCtor, fuelDefault, ctorFr, bodyFrame]
  try rfl

/-- After `balanceOf[msg.sender] = initialSupply;`. -/
def ctorM1 (m : Machine) (w : UInt256) : Machine :=
  { m with evm := (Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner
      (erc20BalanceOfSlot (.address m.evm.executionEnv.source)) w) }

/-- After `totalSupply = initialSupply;`. -/
def ctorM2 (m : Machine) (w : UInt256) : Machine :=
  { ctorM1 m w with evm := (Storage.EVM.storageStore (ctorM1 m w).evm (ctorM1 m w).evm.executionEnv.codeOwner ⟨2⟩ w) }

theorem ctorBody (o : Oracle) (m : Machine) (w : UInt256) :
    ∃ le, ExecBlock erc20Cfg o erc20Flat (ctorFr w) m ctorStmts (.normal (ctorFr w) ((ctorM2 m w).pushLog le)) := by
  obtain ⟨le, hle⟩ := mkLogEntry_evTransfer (ctorM2 m w).this (EVM.address 0) m.evm.executionEnv.source w
  refine ⟨le, ExecBlock.cons (fr1 := ctorFr w) (m1 := ctorM1 m w) ?_
    (ExecBlock.cons (fr1 := ctorFr w) (m1 := ctorM2 m w) ?_
      (ExecBlock.cons (fr1 := ctorFr w) (m1 := (ctorM2 m w).pushLog le) ?_ ExecBlock.nil))⟩
  · refine ExecStmt.exprStmt (EvalExpr.assignPlain (v := u256Val w.toNat) (fr1 := ctorFr w) (m1 := m) rfl
      (EvalExpr.localVal u256 (some .memory) (by frame_simp [ctorFr, bodyFrame, ctorFrameP, immStore,
        Std.HashMap.getElem?_filter']))
      (lvalBalanceOfSender o _ m (by frame_simp [ctorFr, bodyFrame, ctorFrameP, immStore, Std.HashMap.getElem?_filter']))
      ?_)
    exact assign_storage_u256 (erc20Layout_balanceOf m.evm.executionEnv.source m.evm) w
  · refine ExecStmt.exprStmt (EvalExpr.assignPlain (v := u256Val w.toNat) (fr1 := ctorFr w) (m1 := ctorM1 m w) rfl
      (EvalExpr.localVal u256 (some .memory) (by frame_simp [ctorFr, bodyFrame, ctorFrameP, immStore,
        Std.HashMap.getElem?_filter']))
      (EvalLValue.stateVar (by frame_simp [ctorFr, bodyFrame, ctorFrameP, immStore, Std.HashMap.getElem?_filter'])
        erc20Flat_var_totalSupply rfl) ?_)
    exact assign_storage_u256 (erc20Layout_totalSupply (ctorM1 m w).evm) w
  · refine ExecStmt.emit (vs := [.address (EVM.address 0), .address m.evm.executionEnv.source, u256Val w.toNat])
      (fr1 := ctorFr w) (m1 := ctorM2 m w) erc20Flat_event_Transfer rfl ?_ (abiArgs_addr_addr_u256 ..) hle
    refine EvalExprs.cons (fr1 := ctorFr w) (m1 := ctorM2 m w)
      (EvalExpr.convert (v := .literal 0) (fr1 := ctorFr w) (m1 := ctorM2 m w) (EvalExpr.lit rfl)
        (explicitConv_lit0_address ..))
      (EvalExprs.cons (EvalExpr.envMember rfl ?_)
        (EvalExprs.cons (EvalExpr.localVal u256 (some .memory) ?_) EvalExprs.nil))
    · rw [envMember_sender]; simp [ctorM2, ctorM1, storageStore_executionEnv]
    · frame_simp [ctorFr, bodyFrame, ctorFrameP, immStore, Std.HashMap.getElem?_filter']

/-! ## The construction run -/

theorem erc20CtorSpec (o : Oracle) {cA gh bl σ σ₀ g A I} (w : UInt256) (hwv : I.weiValue = ⟨0⟩) :
    ∃ le, solidityCtorExec erc20Cfg o erc20Flat [.int (Int.ofNat w.toNat)] cA gh bl σ σ₀ g A I
      (.ok ((ctorM2 (initMachine cA gh bl σ σ₀ g A I) w).pushLog le) (immStore (ctorFr w))) := by
  obtain ⟨le, hb⟩ := ctorBody o (initMachine cA gh bl σ σ₀ g A I) w
  have hargs : ofAbiList erc20Flat.types ((topCtor? erc20Flat).map (·.decl.params.map (·.ty)) |>.getD [])
      [.int (Int.ofNat w.toNat)] {} = some ([u256Val w.toNat], {}) := by
    simp [erc20Flat_topCtor, fnCtor, ofAbiList, fuelDefault]
  refine ⟨le, solidityCtorExec.run (frP1 := ctorFrameP w) (m1 := initMachine cA gh bl σ σ₀ g A I)
    (ctorPayable_erc20.mpr hwv) erc20Flat_immZero hargs (ctorParam _ w) ?_ ?_⟩
  · rw [erc20Flat_initializers]; exact ExecInits.nil
  · rw [erc20Flat_ctorChain]
    refine ExecCtorChain.run (vs := [u256Val w.toNat]) rfl erc20Flat_fns0 (CtorArgs.top rfl) (ctorEnter _ w)
      EvalMods.nil rfl (ExecChain.body hb) rfl ExecCtorChain.nil

theorem erc20CtorSpecNonPayable (o : Oracle) {cA gh bl σ σ₀ g A I} (args : List Solm.Value) (hwv : I.weiValue ≠ ⟨0⟩) :
    solidityCtorExec erc20Cfg o erc20Flat args cA gh bl σ σ₀ g A I (.reverted ByteArray.empty) :=
  solidityCtorExec.nonPayable (fun h => hwv (ctorPayable_erc20.mp h))

/-! ## The coupled result -/

theorem erc20ConstructorCore : constructorEquivalenceCore erc20Cfg erc20Initcode erc20Flat (constCode erc20Bytecode) := by
  refine constructorEquivalenceCore.intro ?_
  intro cA gh bl σ_evm σ_spec σ₀ g A I args dep hdeploy hcode hcalldata hperm hAccounts
  rw [erc20SolDeployment] at hdeploy
  rcases erc20Deployment_shape hdeploy with ⟨i, hargs, h0, hlt, hdeployed⟩
  subst hargs
  let w : UInt256 := EVM.word i.toNat
  have hlt' : i.toNat < UInt256.size := by
    have h1 : i.toNat < EVM.twoPow 256 := (Int.toNat_lt h0).mpr hlt
    simpa [EVM.twoPow, UInt256.size] using h1
  have hw : i = Int.ofNat w.toNat := by
    have : w.toNat = i.toNat := ulit_toNat' _ hlt'
    rw [this]; exact (Int.toNat_of_nonneg h0).symm
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hcodeCtor : I.code = erc20CtorCode w := by
      rw [hcode, hdeployed]; rfl
    have hX := erc20InitcodeSuccess (createdAccounts := cA) (genesisBlockHeader := gh) (blocks := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) w hcodeCtor hperm hwv
    obtain ⟨le, hspec⟩ := erc20CtorSpec (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀) (g := g) (A := A)
      noOracle w hwv
    rw [← hw] at hspec
    have h := RDret.specCtorCore (runtimeCodeOf := constCode erc20Bytecode) (g := Sat256.ofUInt256 g) noOracle
      hcodeCtor hX hspec
      (by simp [ctorM2, ctorM1, initMachine, initEvm, storageStore_createdAccounts])
      (by
        simp only [pushLog_evm_accountMap, ctorM2, ctorM1, storageStore_accountMap, storageStore_executionEnv,
          initMachine_evm, initState]
        exact accountMapEquiv_sstoreAccountMap_two _ _ _ _ _ _ hAccounts)
      rfl
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
  · let tail := (EVM.Word.toBytesBE w).toByteArray
    have hcodeTail : I.code = erc20Initcode ++ tail := by rw [hcode, hdeployed]
    have hX := erc20InitcodeNonpayableRevert (createdAccounts := cA) (genesisBlockHeader := gh) (blocks := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) tail hcodeTail hwv
    have h := RDrev.specCtorRevertCore (runtimeCodeOf := constCode erc20Bytecode) (args := [Solm.Value.int i])
      (g := Sat256.ofUInt256 g) noOracle hcodeTail hX
      (erc20CtorSpecNonPayable (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀) (g := g) (A := A) noOracle
        [Solm.Value.int i] hwv)
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using h

end ERC20.SolidityProof
