import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeRecipientGuards
import Benchmarks.Morpho.MetaMorphoV1_1.FeeRecipientMutation

/-! The final recipient store and event after interest accrual returns. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem setFeeRecipientStoreReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {w extra : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hcanon : w.toNat < EVM.addressModulus) (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨1239⟩ (w :: extra :: R)
      mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0
      (setFeeRecipientState evm (AccountAddress.ofNat w.toNat)).accountMap ByteArray.empty := by
  have hret := metaMorphoV1_1_block_1239 (immWords := wordsOf (immStore v)) hstack hperm rd
  have hw : UInt256.ofNat (AccountAddress.ofNat w.toNat).toNat = w :=
    addressWord_eq_ofNat_address hcanon
  have hword := setHighAddressWord_bytecode
    (codeOwnerStorageWord evm.executionEnv evm.accountMap (UInt256.ofNat 18))
    (AccountAddress.ofNat w.toNat)
  rw [hw] at hword
  dsimp only [codeOwnerStorageWord] at hword
  rw [hword] at hret
  simpa only [setFeeRecipientState, storageStore_accountMap, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, codeOwnerStorageWord] using hret

end Benchmarks.Morpho.MetaMorphoV1_1
