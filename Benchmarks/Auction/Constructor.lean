import Benchmarks.Auction.Bytecode
import Reasoning.Constructor
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.SolmBody
import Solm.Equiv

/-!
# Auction constructor correctness

The optimized creation bytecode has the standard non-payable guard, then copies the embedded
runtime bytecode window and returns it.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Auction

set_option maxRecDepth 50000000

noncomputable def auctionCtorReturnMem : ByteArray :=
  auctionCreationBytecode.write 29 solcFreePtrMem 0 6150

theorem auctionBytecode_size : auctionBytecode.size = 6150 := by
  native_decide

theorem auctionCreationBytecode_size : auctionCreationBytecode.size = 6179 := by
  native_decide

theorem auctionCreationBytecode_runtime_window :
    auctionCreationBytecode.extract 29 (29 + 6150) = auctionBytecode := by
  native_decide

theorem auctionCtorCodecopyMem :
    auctionCreationBytecode.write 29 solcFreePtrMem 0 6150 = auctionCtorReturnMem := by
  rfl

theorem auctionCtorFinalRead :
    auctionCtorReturnMem.readWithPadding 0 6150 = auctionBytecode := by
  unfold auctionCtorReturnMem
  rw [write0_read_back_from_gen auctionCreationBytecode solcFreePtrMem 29 6150
    (by decide) (by native_decide) (by decide)]
  exact auctionCreationBytecode_runtime_window

set_option maxHeartbeats 800000 in
theorem auctionCtorRunZero {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionCreationBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      auctionBytecode := by
  set s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I with hs0
  have rd0 :
      RD auctionCreationBytecode I g s0 ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0)
        ByteArray.empty (createdAccounts, σ) 0 0 := by
    rw [hs0]; exact RD.initState hcode
  exact evm_run rd0 with [
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue,
    dup1,
    iszero,
    raw push2 ⟨15⟩ (by native_decide) (by evm_ov),
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest,
    pop,
    raw push2 ⟨6150⟩ (by native_decide) (by evm_ov),
    dup1,
    raw push2 ⟨29⟩ (by native_decide) (by evm_ov),
    push0,
    raw codecopy 642 auctionCtorReturnMem (UInt256.ofNat 193) (by native_decide)
      mem_cost
      auctionCtorCodecopyMem
      (by decide) (by evm_ov),
    push0,
    raw ret 0 auctionBytecode (by native_decide)
      mem_cost
      auctionCtorFinalRead
      (by evm_ov)]

set_option maxHeartbeats 500000 in
theorem auctionCtorRunNonzero {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  set s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I with hs0
  have rd0 :
      RD auctionCreationBytecode I g s0 ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0)
        ByteArray.empty (createdAccounts, σ) 0 0 := by
    rw [hs0]; exact RD.initState hcode
  exact evm_run rd0 with [
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue,
    dup1,
    iszero,
    raw push2 ⟨15⟩ (by native_decide) (by evm_ov),
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0,
    dup1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionCtorBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody auctionConfig Auction.auctionContract evm locals
      Auction.auctionContract.ctor.body
      (.returned { contract := Auction.auctionContract, locals := locals } evm none) := by
  change ExecTransitionBody auctionConfig Auction.auctionContract evm locals [nonpayable]
    (.returned { contract := Auction.auctionContract, locals := locals } evm none)
  exact ExecFuncBody.execBlockOK <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run ExecBlock.nil

theorem auctionSolmCtorExecReturn
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdeploy : auctionConfig.selfDeployment auctionCreationBytecode args = some deployedInitcode) :
    solmCtorExec auctionConfig Auction.auctionContract args createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned
        { contract := Auction.auctionContract
          locals := Std.HashMap.ofList
            (List.zip (Auction.auctionContract.ctor.params.map Param.name) args) }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList
      (List.zip (Auction.auctionContract.ctor.params.map Param.name) args))
    ?_ ?_ rfl ?_
  · rfl
  · exact emptyCtorDeployment_args_length (cfg := auctionConfig) (contract := Auction.auctionContract)
      (initcode := auctionCreationBytecode) (deployedInitcode := deployedInitcode)
      (args := args) rfl rfl hdeploy
  · exact auctionCtorBodyReturns _ _ (by simpa [initState] using hwv)

theorem auctionSolmCtorExecRevert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hdeploy : auctionConfig.selfDeployment auctionCreationBytecode args = some deployedInitcode) :
    solmCtorExec auctionConfig Auction.auctionContract args createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList
      (List.zip (Auction.auctionContract.ctor.params.map Param.name) args))
    ?_ ?_ rfl ?_
  · rfl
  · exact emptyCtorDeployment_args_length (cfg := auctionConfig) (contract := Auction.auctionContract)
      (initcode := auctionCreationBytecode) (deployedInitcode := deployedInitcode)
      (args := args) rfl rfl hdeploy
  · change ExecTransitionBody auctionConfig Auction.auctionContract
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
      (Std.HashMap.ofList (List.zip (Auction.auctionContract.ctor.params.map Param.name) args))
      [nonpayable] .reverted
    exact bodyReverts_nonPayable (by simpa [initState] using hwv)

theorem auctionConstructorCorrect :
    constructorEquivalence auctionConfig auctionCreationBytecode Auction.auctionContract auctionBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm hσ
  have hdeployed := emptyCtorDeployment_eq_initcode (cfg := auctionConfig)
    (contract := Auction.auctionContract) (initcode := auctionCreationBytecode)
    (deployedInitcode := deployedInitcode) (args := args) rfl rfl hdeploy
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := auctionCtorRunZero
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hwv
    rcases hrd.xiResult hcode with hoog | ⟨g', A', hsuccess⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
    · refine constructorEquivalenceFor.execution hsuccess
        (auctionSolmCtorExecReturn (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_solm)
          (σ₀ := σ₀) (g := g) (A := A) (I := I) (args := args)
          (deployedInitcode := deployedInitcode) hwv hdeploy) ?_
      exact ctorResultEquiv.success rfl rfl rfl hσ rfl
  · have hrd := auctionCtorRunNonzero
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hwv
    rcases hrd.xiResult hcode with hoog | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
    · refine constructorEquivalenceFor.execution hrev
        (auctionSolmCtorExecRevert (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ_solm)
          (σ₀ := σ₀) (g := g) (A := A) (I := I) (args := args)
          (deployedInitcode := deployedInitcode) hwv hdeploy) ?_
      exact ctorResultEquiv.revert rfl rfl

end Auction
