import Examples.OpenZeppelinBench.Pausable.Bytecode
import Examples.SimpleAuction.Storage
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-!
# Pausable storage helpers

The benchmark has one packed `bool` in slot `0`, byte offset `0`.  Most low-byte storage facts are
reused from `SimpleAuction.Storage`; cross-example reuse here is a library-generalization candidate
for `Reasoning.Storage` / packed scalar storage.
-/

def pausedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def pausedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (pausedRawWord σ I) ⟨255⟩

def pausedSetTrueWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩

def pausedSetFalseWord (w : UInt256) : UInt256 :=
  UInt256.land w (UInt256.lnot ⟨255⟩)

def pausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetTrueWord (pausedRawWord σ I))

def unpausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetFalseWord (pausedRawWord σ I))

def pausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

def unpausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

theorem pausableStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc]
    using SimpleAuction.simpleAuctionStorageLocLoad_bool_offset0 evm slot

theorem pausableStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool false := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc]
    using SimpleAuction.simpleAuctionStorageLocLoad_bool_offset0_false evm slot hzero

theorem pausableStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool true := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc]
    using SimpleAuction.simpleAuctionStorageLocLoad_bool_offset0_true evm slot hnz

theorem pausableStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  simpa [boolLoc, SimpleAuction.simpleAuctionBoolLoc, pausedSetTrueWord]
    using SimpleAuction.simpleAuctionStorageLocStore_bool_true_offset0 evm slot

-- LIBRARY CANDIDATE: `Reasoning.Storage`, packed `bool` store at byte offset 0.
theorem pausablePackedSetFalseWord_eq (w : UInt256) :
    pausedSetFalseWord w = UInt256.ofNat (256 * (w.toNat / 256)) := by
  unfold pausedSetFalseWord
  apply u256_inj
  rw [SimpleAuction.simpleAuctionU256_land_toNat]
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by
    native_decide
  rw [hlnot]
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256
    simpa [UInt256.size] using w.val.isLt
  rw [SimpleAuction.simpleAuctionNatLandClearLow8 w.toNat hwlt]
  have hlt : w.toNat / 2 ^ 8 * 2 ^ 8 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hlt]
  have hlt' : 256 * (w.toNat / 256) < UInt256.size := by
    simpa [Nat.mul_comm] using hlt
  rw [show 2 ^ 8 = 256 by norm_num]
  rw [Nat.mul_comm (w.toNat / 256) 256]
  rw [ulit_toNat' _ hlt']

theorem pausablePackedSetFalseWord_toNat (w : UInt256) :
    (pausedSetFalseWord w).toNat = 256 * (w.toNat / 256) := by
  rw [pausablePackedSetFalseWord_eq]
  have hlt : 256 * (w.toNat / 256) < UInt256.size := by
    have hle : 256 * (w.toNat / 256) ≤ w.toNat :=
      Nat.mul_div_le w.toNat 256
    exact lt_of_le_of_lt hle w.val.isLt
  exact ulit_toNat' _ hlt

-- LIBRARY CANDIDATE: `Reasoning.Storage`, packed `bool` store at byte offset 0.
theorem pausableStorageLocStore_bool_false_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (boolLoc slot) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord boolLoc pausedSetFalseWord
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 0)).1 =
      [0] by native_decide]
  rw [fromBytes'_append, SimpleAuction.simpleAuctionFromBytes'_drop1_wordLE]
  simp [fromBytes']
  simpa [pausedSetFalseWord] using
    (pausablePackedSetFalseWord_toNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).symm

theorem pausableStorageStore_accountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  exact SimpleAuction.simpleAuctionStorageStore_accountMap evm a slot val

theorem pausableStorageStore_createdAccounts
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  exact SimpleAuction.simpleAuctionStorageStore_createdAccounts evm a slot val

-- LIBRARY CANDIDATE: `Reasoning.Storage`; local no-axiom replacement for
-- `accountMapEquiv_sstoreAccountMap`.  This currently names the existing library boundary; before
-- the final axiom gate, replace this with the erased-same-key proof if a final theorem depends on it.
theorem pausableAccountMapEquiv_sstoreAccountMap {σ τ : AccountMap}
    (a : AccountAddress) (slot val : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv (sstoreAccountMap a σ slot val) (sstoreAccountMap a τ slot val) :=
  accountMapEquiv_sstoreAccountMap a slot val hστ

theorem pausePostState_accountMap (evm : EVM.State) :
    (pausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [pausePostState, pausableStorageStore_accountMap]

theorem unpausePostState_accountMap (evm : EVM.State) :
    (unpausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [unpausePostState, pausableStorageStore_accountMap]

theorem pausePostState_createdAccounts (evm : EVM.State) :
    (pausePostState evm).createdAccounts = evm.createdAccounts := by
  simp [pausePostState, pausableStorageStore_createdAccounts]

theorem unpausePostState_createdAccounts (evm : EVM.State) :
    (unpausePostState evm).createdAccounts = evm.createdAccounts := by
  simp [unpausePostState, pausableStorageStore_createdAccounts]

end OpenZeppelinBench.Pausable
