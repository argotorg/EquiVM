import Solidity.Examples.ERC20.Common

/-!
# ERC20 — `totalSupply()` refines its Solidity getter (core relation)

EVM side: the pinned trace `erc20X_totalSupply`.  Spec side: the derivation of the synthesized
getter body `return totalSupply;`.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

/-! ## The spec derivation -/

/-- The getter's frame after entry: one zeroed return slot. -/
def tsFrame : Frame :=
  ({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "#ret0" u256 (some .memory) (u256Val 0)

def tsStmts : Block := [.return (some (.ident "totalSupply"))]

theorem tsEnter (m : Machine) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnTotalSupply.decl [] m = some (.ok (tsFrame, m)) := by
  simp [enterFn, declare, fnTotalSupply, tsFrame, fuelDefault]
  try rfl

abbrev tsWord (m : Machine) : UInt256 := Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner ⟨2⟩
abbrev tsVal (m : Machine) : Value := u256Val (tsWord m).toNat

theorem tsLoad (m : Machine) :
    loadIfScalar erc20Cfg erc20Flat.types m.evm ⟨varTotalSupply.key, []⟩ varTotalSupply.ty = some (tsVal m) :=
  loadIfScalar_u256 (erc20Layout_totalSupply m.evm)

theorem tsBody (o : Oracle) (m : Machine) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame tsFrame tsStmts) m tsStmts
      (.returned ((bodyFrame tsFrame tsStmts).setVal "#ret0" (tsVal m)) m) := by
  refine ExecBlock.consReturn (ExecStmt.returnSingle (r := "#ret0") (v := tsVal m) (fr1 := bodyFrame tsFrame tsStmts)
    (m1 := m) rfl ?_ ?_)
  · refine EvalExpr.stateVar ?_ erc20Flat_var_totalSupply rfl (tsLoad m)
    frame_simp [bodyFrame, tsFrame]
  · frame_simp [assign, coerce, bodyFrame, tsFrame]
    try rfl

theorem tsCall (o : Oracle) (m : Machine) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTotalSupply [] (.ok [tsVal m] m) := by
  refine CallFn.ok (tsEnter m) rfl (ExecChain.body (tsBody o m)) rfl ?_
  frame_simp [retVals, bodyFrame, tsFrame]

theorem erc20TotalSupplySpec (o : Oracle) {cA gh bl σ σ₀ g A I}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned (initMachine cA gh bl σ σ₀ g A I) [.int (Int.ofNat (totalSupplyWord σ I).toNat)])
      (.abi [abiU256]) := by
  have hsz := size_ge_of_sel rfl hsel
  have hsvs : decodeArgs erc20Cfg erc20Flat.types fnTotalSupply.decl I.calldata = some [] := by
    rw [decodeArgs_unfold _ _ sigTotalSupply sigOf_totalSupply]
    exact decodeCalldataValues_empty_ok hsz
  have hout : [tsVal (initMachine cA gh bl σ σ₀ g A I)].mapM (toAbi (initMachine cA gh bl σ σ₀ g A I).heap fuelDefault) =
      some [.int (Int.ofNat (totalSupplyWord σ I).toNat)] := by
    simp [fuelDefault]
    rfl
  exact solidityExec.call (erc20Dispatch_totalSupply hsel) erc20Flat_fns6 (Or.inr hwv) rfl hsvs rfl
    (tsCall o (initMachine cA gh bl σ σ₀ g A I)) hout

/-! ## The coupled result -/

theorem erc20TotalSupplyCore {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨148⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hX := erc20X_totalSupply (g := Sat256.ofUInt256 g) hreach
  have hword : totalSupplyWord σ_evm I = totalSupplyWord σ_spec I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have h := RDret.specExecutionCore (g := Sat256.ofUInt256 g) noOracle hcode hX
    (erc20TotalSupplySpec noOracle hsel hwv) rfl hAccounts
    (.abi (by rw [hword]; exact uint256ReturnEncoding _))
  simpa [Sat256.ofUInt256, Sat256.toUInt256] using h

end ERC20.SolidityProof
