import Benchmarks.Safe.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a nonpayable getter for a uint256 scalar storage location.
theorem uint256GetterBodyReturns {cfg : Config} {c : ContractDecl} {layout : StorageLayout}
    {imms : Store} (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef cfg { contract := c, locals := locals, immutables := imms }
      evm ref = .ok er)
    (hty : storageTypeAt? c.storage er = some (.elem (.int (.uint ⟨256, by decide⟩))))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf (uint256Loc slot))) :
    ExecTransitionBody cfg c evm locals
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [.storage ref]]
      (.returned { contract := c, locals := locals, immutables := imms } evm
        (some [.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat)])) imms := by
  apply nonpayableReturnExprBodyReturns h
  exact evalExpr_storage_scalar_value hbase her hty hbackend hloc
    (storageLocLoad_uint256 evm slot)

end Benchmarks.Safe
