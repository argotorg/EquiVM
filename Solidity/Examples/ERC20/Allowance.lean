import Solidity.Examples.ERC20.Common

/-!
# ERC20 — `allowance(address,address)` refines its Solidity getter (core relation)
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

/-! ## Arguments -/

theorem erc20Args_allowance_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hcanon0 : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanon1 : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata =
      some [.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat),
        .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)] := by
  rw [decodeArgs_unfold _ _ sigAllowance sigOf_allowance]
  exact decodeCalldataValues_address_address_ok hsz68 hbig hcanon0 hcanon1

theorem erc20Args_allowance_none_short {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68) :
    decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigAllowance sigOf_allowance]
  exact decodeCalldataValues_address_address_none_short hsz4 hshort

theorem erc20Args_allowance_none_noncanon0 {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hnc : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigAllowance sigOf_allowance]
  exact decodeCalldataValues_address_address_none_noncanon0 hsz68 hbig hnc

theorem erc20Args_allowance_none_noncanon1 {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hcanon0 : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigAllowance sigOf_allowance]
  exact decodeCalldataValues_address_address_none_noncanon1 hsz68 hbig hcanon0 hnc

theorem erc20Args_allowance_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigAllowance sigOf_allowance]
  exact decodeCalldataValues_address_address_none_huge hbig

/-! ## The spec derivation -/

def alFrame (a b : EVM.Address) : Frame :=
  ((({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "arg0" addrTy (some .memory) (.address a)).bind
    "arg1" addrTy (some .memory) (.address b)).bind "#ret0" u256 (some .memory) (u256Val 0)

def alStmts : Block := [.return (some (.index (.index (.ident "allowance") (.ident "arg0")) (.ident "arg1")))]

theorem alEnter (m : Machine) (a b : EVM.Address) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnAllowance.decl [.address a, .address b] m =
      some (.ok (alFrame a b, m)) := by
  simp [enterFn, declare, coerce, fnAllowance, alFrame, fuelDefault]
  try rfl

abbrev alWord (m : Machine) (a b : EVM.Address) : UInt256 :=
  Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner (erc20AllowanceSlot (.address a) (.address b))
abbrev alVal (m : Machine) (a b : EVM.Address) : Value := u256Val (alWord m a b).toNat

/-- `allowance[k1][k2]` for local addresses `k1`, `k2`. -/
theorem evalAllowanceIndex (o : Oracle) (fr : Frame) (m : Machine) (x y : Ident) (a b : EVM.Address)
    (hx : fr.get? x = some { ty := addrTy, loc := some .memory, val := .address a })
    (hy : fr.get? y = some { ty := addrTy, loc := some .memory, val := .address b })
    (hb : fr.get? "allowance" = none) :
    EvalExpr erc20Cfg o erc20Flat fr m (.index (.index (.ident "allowance") (.ident x)) (.ident y))
      (.ok (alVal m a b) fr m) := by
  have h1 : EvalExpr erc20Cfg o erc20Flat fr m (.index (.ident "allowance") (.ident x))
      (.ok (.storageRef ⟨"allowance", [.mindex (.address a)]⟩ (.mapping addrTy u256)) fr m) :=
    EvalExpr.indexStorage (EvalExpr.stateVar hb erc20Flat_var_allowance rfl (loadIfScalar_mapping ..))
      (EvalExpr.local hx) (storageIndex_mapping_address ..) (loadIfScalar_mapping ..)
  exact EvalExpr.indexStorage h1 (EvalExpr.local hy) (storageIndex_mapping_address ..)
    (loadIfScalar_u256 (env := erc20Flat.types) (erc20Layout_allowance a b m.evm))

theorem alBody (o : Oracle) (m : Machine) (a b : EVM.Address) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (alFrame a b) alStmts) m alStmts
      (.returned ((bodyFrame (alFrame a b) alStmts).setVal "#ret0" (alVal m a b)) m) := by
  refine ExecBlock.consReturn (ExecStmt.returnSingle (r := "#ret0") (v := alVal m a b)
    (fr1 := bodyFrame (alFrame a b) alStmts) (m1 := m) rfl ?_ ?_)
  · exact evalAllowanceIndex o _ m "arg0" "arg1" a b (by frame_simp [bodyFrame, alFrame])
      (by frame_simp [bodyFrame, alFrame]) (by frame_simp [bodyFrame, alFrame])
  · frame_simp [assign, coerce, bodyFrame, alFrame]
    try rfl

theorem alCall (o : Oracle) (m : Machine) (a b : EVM.Address) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnAllowance [.address a, .address b]
      (.ok [alVal m a b] m) := by
  refine CallFn.ok (alEnter m a b) EvalMods.nil rfl (ExecChain.body (alBody o m a b)) rfl ?_
  frame_simp [retVals, bodyFrame, alFrame]

theorem erc20AllowanceSpec (o : Oracle) {cA gh bl σ σ₀ g A I}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanon1 : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned (initMachine cA gh bl σ σ₀ g A I) [.int (Int.ofNat (allowanceWord σ I).toNat)])
      (.abi [abiU256]) := by
  have hout : [alVal (initMachine cA gh bl σ σ₀ g A I) (AccountAddress.ofNat (allowanceOwnerWord I).toNat)
      (AccountAddress.ofNat (allowanceSpenderWord I).toNat)].mapM
      (toAbi (initMachine cA gh bl σ σ₀ g A I).heap fuelDefault) =
      some [.int (Int.ofNat (allowanceWord σ I).toNat)] := by
    simp [fuelDefault]
    rfl
  exact solidityExec.call (erc20Dispatch_allowance hsel) erc20Flat_fns5 (Or.inr hwv) rfl
    (erc20Args_allowance_ok hsz68 hbig hcanon0 hcanon1) (by simp [ofAbiList, fnAllowance, fuelDefault])
    (alCall o (initMachine cA gh bl σ σ₀ g A I) _ _) hout

theorem erc20AllowanceRejects {I : ExecutionEnv}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hdec : decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata = none)
    {cA gh bl σ_evm σ_spec σ₀ A} {g : UInt256} (hcode : I.code = erc20Bytecode)
    (h : RDrev erc20Bytecode (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have := RDrev.specDecodingFailedCore (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode h
    (erc20Dispatch_allowance hsel) erc20Flat_fns5 (Or.inr hwv) hdec
  simpa [Sat256.ofUInt256, Sat256.toUInt256] using this

/-! ## The coupled result -/

theorem erc20AllowanceCore {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨322⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hsz4 := erc20AllowanceSelector_size hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon0 : (allowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanon1 : (allowanceSpenderWord I).toNat < EVM.addressModulus
        · have hX := erc20X_allowance (g := Sat256.ofUInt256 g) hsz68 hsize hbig hcanon0 hcanon1 hreach
          have hword : allowanceWord σ_evm I = allowanceWord σ_spec I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceSlot I) ⟨0⟩
          have h := RDret.specExecutionCore (g := Sat256.ofUInt256 g) noOracle hcode hX
            (erc20AllowanceSpec noOracle hsel hwv hsz68 hbig hcanon0 hcanon1) rfl hAccounts
            (.abi (by rw [hword]; exact uint256ReturnEncoding _))
          simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
        · have hnc : UInt256.eq (allowanceSpenderWord I)
              (UInt256.land (allowanceSpenderWord I) erc20AddrMask) = ⟨0⟩ :=
            erc20Ueq_zero_of_ne (fun he => hcanon1 (erc20Word_canonical_of_clean he))
          exact erc20AllowanceRejects hsel hwv (erc20Args_allowance_none_noncanon1 hsz68 hbig hcanon0 hcanon1) hcode
            (erc20AllowanceX_noncanon_spender (g := Sat256.ofUInt256 g) hsz68 hsize hbig hcanon0 hnc hreach)
      · have hnc : UInt256.eq (allowanceOwnerWord I)
            (UInt256.land (allowanceOwnerWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanon0 (erc20Word_canonical_of_clean he))
        exact erc20AllowanceRejects hsel hwv (erc20Args_allowance_none_noncanon0 hsz68 hbig hcanon0) hcode
          (erc20AllowanceX_noncanon_owner (g := Sat256.ofUInt256 g) hsz68 hsize hbig hnc hreach)
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact erc20AllowanceRejects hsel hwv (erc20Args_allowance_none_huge hbigge) hcode
        (erc20AllowanceX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
  · have hshort : I.calldata.size < 68 := by omega
    exact erc20AllowanceRejects hsel hwv (erc20Args_allowance_none_short hsz4 hshort) hcode
      (erc20AllowanceX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)

end ERC20.SolidityProof
