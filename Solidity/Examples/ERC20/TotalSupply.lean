import Solidity.Examples.ERC20.Shapes

/-!
# ERC20 — `totalSupply()` refines its Solidity getter

EVM side: the body at `0x8c` loads slot 2 and returns it through the one-word tail.  Spec side:
the synthesized getter `return totalSupply;`.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-! ## The EVM run -/

theorem tsRun {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 1)) :
    Returned erc20Runtime (initState σ σ₀ g A I) ⟨A.createdAccounts, σ, A.logSeries⟩
      (UInt256.toByteArray (solcSlotWord σ I ⟨2⟩)) := by
  obtain ⟨_, _, h⟩ := reachBodyOf 1 (by omega) ⟨0x8c⟩ hcode hwv hsize hsel (by jump_dest) (by decide)
  have h1 := evm_run h with [jumpdest, push2 ⟨0x95⟩, push1 ⟨2⟩]
  obtain ⟨_, _, h2⟩ := h1.sload (by native_decide) (by evm_ov)
  have h3 := evm_run h2 with [dup2, jump (by jump_dest)]
  exact retWord h3 (by simp [solcFreePtrMem_size]) solcFreePtrMem_read64 solcFreePtrMem_gap (by simp)

/-! ## The spec derivation -/

def tsFrame : Frame :=
  ({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "#ret0" u256 (some .memory) (u256Val 0)

def tsStmts : Block := [.return (some (.ident "totalSupply"))]

theorem tsEnter (m : Machine) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnTotalSupply.decl [] m = some (.ok (tsFrame, m)) := by
  simp [enterFn, declare, fnTotalSupply, tsFrame, fuelDefault]
  try rfl

theorem tsBody (o : Oracle) (m : Machine) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame tsFrame tsStmts) m tsStmts
      (.returned ((bodyFrame tsFrame tsStmts).setVal "#ret0" (u256Val (loadU256 m ⟨2⟩).toNat)) m) :=
  ExecBlock.consReturn (ExecStmt.returnU256 { ty := u256, loc := some .memory, val := u256Val 0 } rfl
    (EvalExpr.stateU256 (by frame_simp [bodyFrame, tsFrame]) erc20Flat_var_totalSupply rfl rfl
      (erc20Leaf_totalSupply))
    (by frame_simp [bodyFrame, tsFrame]) rfl (by frame_simp [bodyFrame, tsFrame]))

theorem tsCall (o : Oracle) (m : Machine) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTotalSupply [] (.ok [u256Val (loadU256 m ⟨2⟩).toNat] m) :=
  CallFn.plain (tsEnter m) rfl rfl (tsBody o m) rfl
    (retVals_exitScope (by frame_simp [bodyFrame, tsFrame]) (by frame_simp [bodyFrame, tsFrame])
      (by frame_simp [retVals, bodyFrame, tsFrame]))

theorem tsSpec (o : Oracle) {σ σ₀ g A I} (hsel : selIs I (selBytes 1)) (hwv : I.weiValue = ⟨0⟩) :
    solidityExec erc20Cfg o erc20Flat ∅ σ σ₀ g A I
      (.returned (initMachine σ σ₀ g A I ∅)
        [.int ((loadU256 (initMachine σ σ₀ g A I ∅) ⟨2⟩).toNat : Int)])
      (.abi [abiU256]) := by
  have hsz : 4 ≤ I.calldata.size := size_ge_of_sel rfl hsel
  have hsvs : decodeArgs erc20Cfg erc20Flat.types fnTotalSupply.decl I.calldata = some [] := by
    rw [decodeArgs_totalSupply]; exact decodeCalldataValues_empty_ok hsz
  have hprep : prepareArgs erc20Flat.types I.calldata fuelDefault (initMachine σ σ₀ g A I ∅).heap
      [u256Val (loadU256 (initMachine σ σ₀ g A I ∅) ⟨2⟩).toNat] =
      some (.ok ([u256Val (loadU256 (initMachine σ σ₀ g A I ∅) ⟨2⟩).toNat],
        (initMachine σ σ₀ g A I ∅).heap)) :=
    prepareArgs_of_noRaw (fuel := 1023) (by simp [fuelDefault, u256Val])
  exact solidityExec.call (erc20Dispatch_totalSupply hsel) erc20Flat_fns6 (Or.inr hwv) rfl hsvs rfl
    (tsCall o (initMachine σ σ₀ g A I ∅)) hprep (by simp [fuelDefault, u256Val])

/-! ## The coupled result -/

theorem totalSupplyCorrect {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Runtime) (hsize : I.calldata.size < UInt256.size) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selBytes 1)) :
    runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := by
  have hw : WorldEquiv ⟨A.createdAccounts, σ, A.logSeries⟩ (initMachine σ σ₀ g A I ∅) := WorldEquiv.init ∅ {}
  have hword : solcSlotWord σ I ⟨2⟩ = loadU256 (initMachine σ σ₀ g A I ∅) ⟨2⟩ := hw.sload rfl ⟨2⟩
  refine Returned.specExecutionW default hcode (tsRun hcode hwv hsize hsel) (tsSpec default hsel hwv) hw ?_
  rw [hword]
  exact .abi (uint256ReturnEncoding _)

end ERC20.Opt
