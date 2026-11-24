import Benchmarks.Auction.OwnerSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem scalarWrite (evm evm' : EVM.State) (locals : Store) (name : Ident)
    (ty : StorageType) (loc : StorageLoc) (value : Value)
    (hbase : locals.get? name = none)
    (hty : storageTypeAt? auctionContract.storage { base := name } = some ty)
    (hloc : auctionConfig.storageBackend.locate? { base := name } = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm
      .storage { base := name } value =
        .ok ({ contract := auctionContract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value (hbackend := rfl) hbase _ hty hloc hleaf hstore
  simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem ownerSetUint256Split (evm : EVM.State) (locals : Store) (name param : Ident)
    (slot value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (howner : locals.get? "_owner" = none) (hbase : locals.get? name = none)
    (hparam : locals.get? param = some (.int (Int.ofNat value.toNat)))
    (hty : storageTypeAt? auctionContract.storage { base := name } =
      some (.elem (.int uint256Int)))
    (hloc : auctionConfig.storageBackend.locate? { base := name } =
      some (.leaf (auctionUint256Loc slot))) :
    (evm.executionEnv.perm = true → ExecTransitionBody fork auctionConfig auctionContract evm locals
      [nonpayable, .require (.binary .eq sender (.storage ownerRef)),
        .assign .storage { base := name } (.var param)]
      (.returned { contract := auctionContract, locals := locals }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot value) none)) ∧
      (evm.executionEnv.perm = false → ExecTransitionBody fork auctionConfig auctionContract evm locals
        [nonpayable, .require (.binary .eq sender (.storage ownerRef)),
          .assign .storage { base := name } (.var param)] .staticViolation) := by
  have hownerEval := evalOwnerEq_true evm locals howner ho
  have hvalue : evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.var param) = .ok (.int (Int.ofNat value.toNat)) := by
    simp only [evalExpr?, hparam, EvalResult.ofOption]
  have hassign := scalarWrite evm _ locals name (.elem (.int uint256Int))
    (auctionUint256Loc slot) _ hbase hty hloc
    (by exact Or.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm slot value)
  constructor
  · intro hperm
    exact ExecFuncBody.execBlockOK
      (nonpayableRequireAssignStorageBlock hwv hownerEval hvalue hassign hperm)
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (nonpayableRequireAssignStorageBlockStatic hwv hownerEval hvalue hassign hperm)

theorem ownerBodyReverts (evm : EVM.State) (locals : Store) (rest : List Stmt)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv ≠ ownerWord evm.accountMap evm.executionEnv)
    (howner : locals.get? "_owner" = none) :
    ExecTransitionBody fork auctionConfig auctionContract evm locals
      (nonpayable :: .require (.binary .eq sender (.storage ownerRef)) :: rest) .reverted :=
  ExecFuncBody.execBlockRevert <|
    nonpayableSecondRequireReverts hwv (evalOwnerEq_false evm locals howner ho)

end Auction
