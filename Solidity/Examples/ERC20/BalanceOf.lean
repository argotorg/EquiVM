import Solidity.Examples.ERC20.Common

/-!
# ERC20 — `balanceOf(address)` refines its Solidity getter (core relation)
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

/-! ## Arguments -/

theorem erc20Args_balanceOf_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl I.calldata = some [balanceOfOwnerValue I] := by
  rw [decodeArgs_unfold _ _ sigBalanceOf sigOf_balanceOf]
  have h := decodeCalldata_address_ok (cd := I.calldata) (x := "arg0") hsz36 hbig hcanon
  simp only [fnBalanceOf, List.zipIdx, List.map, paramName, Option.getD, sigBalanceOf]
  rw [h]
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, balanceOfOwnerValue, balanceOfOwnerWord,
    calldataWord, -getElem?_pos, -getElem?_neg]
  rfl

theorem erc20Args_balanceOf_none_short {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) :
    decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigBalanceOf sigOf_balanceOf]
  simp only [fnBalanceOf, List.zipIdx, List.map, paramName, Option.getD, sigBalanceOf]
  rw [decodeCalldata_address_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort]
  rfl

theorem erc20Args_balanceOf_none_noncanon {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hnc : ¬ (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigBalanceOf sigOf_balanceOf]
  simp only [fnBalanceOf, List.zipIdx, List.map, paramName, Option.getD, sigBalanceOf]
  rw [decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "arg0") hsz36 hbig hnc]
  rfl

theorem erc20Args_balanceOf_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigBalanceOf sigOf_balanceOf]
  simp only [fnBalanceOf, List.zipIdx, List.map, paramName, Option.getD, sigBalanceOf]
  rw [decodeCalldata_address_none_huge (cd := I.calldata) (x := "arg0") hbig]
  rfl

/-! ## The spec derivation -/

/-- The getter's frame after entry: the owner and one zeroed return slot. -/
def boFrame (a : EVM.Address) : Frame :=
  (({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "arg0" addrTy (some .memory) (.address a)).bind
    "#ret0" u256 (some .memory) (u256Val 0)

def boStmts : Block := [.return (some (.index (.ident "balanceOf") (.ident "arg0")))]

theorem boEnter (m : Machine) (a : EVM.Address) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnBalanceOf.decl [.address a] m = some (.ok (boFrame a, m)) := by
  simp [enterFn, declare, coerce, fnBalanceOf, boFrame, fuelDefault]
  try rfl

abbrev boWord (m : Machine) (a : EVM.Address) : UInt256 :=
  Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner (erc20BalanceOfSlot (.address a))
abbrev boVal (m : Machine) (a : EVM.Address) : Value := u256Val (boWord m a).toNat

/-- `balanceOf[k]` for a local address `k`. -/
theorem evalBalanceOfIndex (o : Oracle) (fr : Frame) (m : Machine) (x : Ident) (a : EVM.Address)
    (hx : fr.get? x = some { ty := addrTy, loc := some .memory, val := .address a })
    (hb : fr.get? "balanceOf" = none) :
    EvalExpr erc20Cfg o erc20Flat fr m (.index (.ident "balanceOf") (.ident x)) (.ok (boVal m a) fr m) := by
  refine EvalExpr.indexStorage (EvalExpr.stateVar hb erc20Flat_var_balanceOf rfl (loadIfScalar_mapping ..))
    (EvalExpr.local hx) (storageIndex_mapping_address ..) ?_
  simpa using loadIfScalar_u256 (env := erc20Flat.types) (erc20Layout_balanceOf a m.evm)

theorem boBody (o : Oracle) (m : Machine) (a : EVM.Address) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (boFrame a) boStmts) m boStmts
      (.returned ((bodyFrame (boFrame a) boStmts).setVal "#ret0" (boVal m a)) m) := by
  refine ExecBlock.consReturn (ExecStmt.returnSingle (r := "#ret0") (v := boVal m a)
    (fr1 := bodyFrame (boFrame a) boStmts) (m1 := m) rfl ?_ ?_)
  · exact evalBalanceOfIndex o _ m "arg0" a (by frame_simp [bodyFrame, boFrame]) (by frame_simp [bodyFrame, boFrame])
  · frame_simp [assign, coerce, bodyFrame, boFrame]
    try rfl

theorem boCall (o : Oracle) (m : Machine) (a : EVM.Address) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnBalanceOf [.address a] (.ok [boVal m a] m) := by
  refine CallFn.ok (boEnter m a) EvalMods.nil rfl (ExecChain.body (boBody o m a)) rfl ?_
  frame_simp [retVals, bodyFrame, boFrame]

theorem erc20BalanceOfSpec (o : Oracle) {cA gh bl σ σ₀ g A I}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned (initMachine cA gh bl σ σ₀ g A I) [.int (Int.ofNat (balanceOfWord σ I).toNat)])
      (.abi [abiU256]) := by
  have hout : [boVal (initMachine cA gh bl σ σ₀ g A I) (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)].mapM
      (toAbi (initMachine cA gh bl σ σ₀ g A I).heap fuelDefault) =
      some [.int (Int.ofNat (balanceOfWord σ I).toNat)] := by
    simp [fuelDefault]
    rfl
  exact solidityExec.call (erc20Dispatch_balanceOf hsel) erc20Flat_fns4 (Or.inr hwv) rfl
    (erc20Args_balanceOf_ok hsz36 hbig hcanon) (by simp [ofAbiList, fnBalanceOf, fuelDefault])
    (boCall o (initMachine cA gh bl σ σ₀ g A I) _) hout

/-- The spec dispatches to `balanceOf` but rejects the calldata. -/
theorem erc20BalanceOfRejects {I : ExecutionEnv}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hdec : decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl I.calldata = none)
    {cA gh bl σ_evm σ_spec σ₀ A} {g : UInt256} (hcode : I.code = erc20Bytecode)
    (h : RDrev erc20Bytecode (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have := RDrev.specDecodingFailedCore (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode h (erc20Dispatch_balanceOf hsel)
    erc20Flat_fns4 (Or.inr hwv) hdec
  simpa [Sat256.ofUInt256, Sat256.toUInt256] using this

/-! ## The coupled result -/

theorem erc20BalanceOfCore {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨226⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hsz4 := erc20BalanceOfSelector_size hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus
      · have hX := erc20X_balanceOf (g := Sat256.ofUInt256 g) hsz36 hsize hbig hcanon hreach
        have hword : balanceOfWord σ_evm I = balanceOfWord σ_spec I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (balanceOfSlot I) ⟨0⟩
        have h := RDret.specExecutionCore (g := Sat256.ofUInt256 g) noOracle hcode hX
          (erc20BalanceOfSpec noOracle hsel hwv hsz36 hbig hcanon) rfl hAccounts
          (.abi (by rw [hword]; exact uint256ReturnEncoding _))
        simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
      · have hnc : UInt256.eq (balanceOfOwnerWord I)
            (UInt256.land (balanceOfOwnerWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanon (erc20Word_canonical_of_clean he))
        exact erc20BalanceOfRejects hsel hwv (erc20Args_balanceOf_none_noncanon hsz36 hbig hcanon) hcode
          (erc20BalanceOfX_noncanon (g := Sat256.ofUInt256 g) hsz36 hsize hbig hnc hreach)
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact erc20BalanceOfRejects hsel hwv (erc20Args_balanceOf_none_huge hbigge) hcode
        (erc20BalanceOfX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
  · have hshort : I.calldata.size < 36 := by omega
    exact erc20BalanceOfRejects hsel hwv (erc20Args_balanceOf_none_short hsz4 hshort) hcode
      (erc20BalanceOfX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)

end ERC20.SolidityProof
