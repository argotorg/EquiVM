import Benchmarks.Morpho.MetaMorphoV1_1.MintInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_079

/-! The checked supply addition and ordered storage updates of the compiled mint helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def mintTransferTopic : UInt256 :=
  UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991

def mintWorkStack (recipient : AccountAddress) (value ret : UInt256) (R : List UInt256) :
    List UInt256 :=
  value :: ⟨32⟩ :: mintTransferTopic :: ⟨0⟩ :: UInt256.ofNat recipient.toNat :: ret :: R

def mintReturnMemory (mem : ByteArray) (recipient : AccountAddress) (value : UInt256) :
    ByteArray :=
  let scratch := twoWordHashMem (UInt256.ofNat recipient.toNat) ⟨0⟩ mem
  writeWord scratch (memLoad ⟨64⟩ scratch).toNat value

theorem mintReachAdd {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hto : recipient ≠ AccountAddress.ofNat 0)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨17718⟩
      (UInt256.ofNat recipient.toNat :: value :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨12077⟩
      (mintOldSupply evm :: value :: ⟨17783⟩ :: mintWorkStack recipient value ret R)
      mem aw' rdata evm.accountMap k' C' := by
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat recipient.toNat) = UInt256.ofNat recipient.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical recipient)
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17718_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [hm]; exact isZero_eq_zero_of_ne (approvalAddressWord_ne_zero hto)) rd
  simp only [metaMorphoV1_1_block_17718_fallthrough_stack, hm] at h1
  exact metaMorphoV1_1_block_17735_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem mintReachStore {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hgood : mintAllowed evm recipient value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨17718⟩
      (UInt256.ofNat recipient.toNat :: value :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨17783⟩
      ((mintOldSupply evm + value) :: mintWorkStack recipient value ret R)
      mem aw' rdata evm.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := mintReachAdd v hstack hgood.1 rd
  obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
    (by simp only [mintWorkStack, List.length_cons]; omega) hgood.2
    (by change (D_J (immutableLayout.runtime metaMorphoV1_1Bytecode
          (wordsOf (immStore v))) 0).contains ⟨17783⟩ = true
        rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact ⟨aw1, k2, C2, h2⟩

theorem mintReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hgood : mintAllowed evm recipient value) (hperm : evm.executionEnv.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨17718⟩
      (UInt256.ofNat recipient.toNat :: value :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ret R
      (mintReturnMemory mem recipient value) aw' rdata
      (mintBalanceState evm recipient value).accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := mintReachStore v hstack hgood rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17783_packed
    (immWords := wordsOf (immStore v)) (by omega) hperm hret h1
  let scratch := twoWordHashMem (UInt256.ofNat recipient.toNat) ⟨0⟩ mem
  have hh : keccakWord ⟨0⟩ ⟨64⟩ scratch = balanceSlot recipient :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD (deployedRuntime v) evm.executionEnv g s0 ret R
    (mintReturnMemory mem recipient value) aw2 rdata
    (sstoreAccountMap evm.executionEnv.codeOwner
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨2⟩ (mintOldSupply evm + value))
      (keccakWord ⟨0⟩ ⟨64⟩ scratch)
      (codeOwnerStorageWord evm.executionEnv
        (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨2⟩ (mintOldSupply evm + value))
        (keccakWord ⟨0⟩ ⟨64⟩ scratch) + value)) k2 C2 at h2
  rw [hh] at h2
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [mintBalanceState, balanceStore, balanceWord, storageStore_accountMap,
    mintSupplyState, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, codeOwnerStorageWord] using h2

theorem mintRevert {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbad : ¬ mintAllowed evm recipient value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨17718⟩
      (UInt256.ofNat recipient.toNat :: value :: ret :: R) mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hto : recipient ≠ AccountAddress.ofNat 0
  · obtain ⟨aw1, k1, C1, h1⟩ := mintReachAdd v hstack hto rd
    exact checkedAddRevert v (by simp only [mintWorkStack, List.length_cons]; omega)
      (Nat.le_of_not_gt (fun hfit ↦ hbad ⟨hto, hfit⟩)) h1
  · have hz : recipient = AccountAddress.ofNat 0 := not_ne_iff.mp hto
    subst recipient
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17718_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_12879 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_17718_taken_stack, List.length_cons]; omega) h1

theorem mintStatic {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hgood : mintAllowed evm recipient value) (hperm : evm.executionEnv.perm = false)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨17718⟩
      (UInt256.ofNat recipient.toNat :: value :: ret :: R) mem aw rdata evm.accountMap k C) :
    RDstatic (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := mintReachStore v hstack hgood rd
  have r1 := h1.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨17783⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (by simp only [mintWorkStack, List.length_cons]; omega)
  have r2 := r1.push1 (UInt256.ofNat 2) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨17784⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1),
      immutableLayout_inBounds, immutableTemplate_size64))
    (by simp only [mintWorkStack, List.length_cons]; omega)
  exact r2.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨17786⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (by simp only [mintWorkStack, List.length_cons]; omega)

end Benchmarks.Morpho.MetaMorphoV1_1
