import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeGuards
import Benchmarks.Morpho.MetaMorphoV1_1.FeeMutation

/-! The final fee store and event after interest accrual returns. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem setFeeStoreReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨7511⟩
      (w :: UInt256.ofNat (2 ^ 96 - 1) :: R) mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (setFeeState evm w).accountMap ByteArray.empty := by
  have hret := metaMorphoV1_1_block_7511 (immWords := wordsOf (immStore v)) hstack hperm rd
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 96 - 1) := by decide
  rw [hm] at hret
  have hword := setFeeWord_bytecode
    (codeOwnerStorageWord evm.executionEnv evm.accountMap (UInt256.ofNat 18)) w
  dsimp only [codeOwnerStorageWord] at hword
  rw [u256_lor_comm, u256_land_comm
    (evm.accountMap.get? evm.executionEnv.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat 18) (⟨0⟩ : UInt256)))] at hret
  rw [hword] at hret
  simpa only [setFeeState, storageStore_accountMap, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, codeOwnerStorageWord] using hret

end Benchmarks.Morpho.MetaMorphoV1_1
