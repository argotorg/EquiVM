import Benchmarks.Auction.OwnerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem scalarWrite (evm evm' : EVM.State) (locals : Store) (name : Ident)
    (ty : StorageType) (loc : StorageLoc) (value : Value)
    (hbase : locals.get? name = none)
    (hty : storageTypeAt? auctionContract.storage { base := name } = some ty)
    (hloc : auctionConfig.storage.layout { base := name } = fun _ => some loc)
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True)
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm
      .storage { base := name } value =
        .ok ({ contract := auctionContract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value hbase _ hty hloc hscalar hstore
  simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem ownerSetUint256 (evm : EVM.State) (locals : Store) (name param : Ident)
    (slot value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (howner : locals.get? "_owner" = none) (hbase : locals.get? name = none)
    (hparam : locals.get? param = some (.int (Int.ofNat value.toNat)))
    (hty : storageTypeAt? auctionContract.storage { base := name } =
      some (.elem (.int uint256Int)))
    (hloc : auctionConfig.storage.layout { base := name } =
      fun _ => some (auctionUint256Loc slot)) :
    ExecTransitionBody auctionConfig auctionContract evm locals
      [nonpayable, .require (.binary .eq sender (.storage ownerRef)),
        .assign .storage { base := name } (.var param)]
      (.returned { contract := auctionContract, locals := locals }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value) none) := by
  apply ExecFuncBody.execBlockOK
  apply nonpayableRequireAssignStorageBlock (value := .int (Int.ofNat value.toNat))
    hwv (evalOwnerEq_true evm locals howner ho)
  · simp only [evalExpr?, hparam, EvalResult.ofOption]
  · exact scalarWrite evm _ locals name (.elem (.int uint256Int))
      (auctionUint256Loc slot) _ hbase hty hloc
      (by trivial) (storageLocStore_uint256 evm slot value)

theorem ownerBodyReverts (evm : EVM.State) (locals : Store) (rest : List Stmt)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv ≠ ownerWord evm.accountMap evm.executionEnv)
    (howner : locals.get? "_owner" = none) :
    ExecTransitionBody auctionConfig auctionContract evm locals
      (nonpayable :: .require (.binary .eq sender (.storage ownerRef)) :: rest) .reverted :=
  ExecFuncBody.execBlockRevert <|
    nonpayableSecondRequireReverts hwv (evalOwnerEq_false evm locals howner ho)

end Auction
