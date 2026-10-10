import Benchmarks.Morpho.MetaMorphoV1_1.StringClearStorage
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageWrite

/-! Relate the storage writer's account maps to the source state, without slot assumptions. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem storageStringPacked (evm : State) (slot : UInt256)
    (hvalid : storageStringValid (storageStringHeader evm slot)) :
    checkBytesPacked slot evm =
      decide ((storageStringLength (storageStringHeader evm slot)).toNat < 32) := by
  by_cases hf : UInt256.land (storageStringHeader evm slot) ⟨1⟩ = ⟨0⟩
  · rw [checkBytesPacked_of_storageLoad_land_one_zero rfl hf,
      decide_eq_true (storageStringShortLength _ hvalid hf)]
  · rw [checkBytesPacked_of_storageLoad_land_one_ne_zero rfl hf,
      decide_eq_false (Nat.not_lt.mpr (storageStringLongLength _ hvalid hf))]

theorem storageStringWriteState_accounts (evm : State) (symbol : Bool) (bytes : ByteArray)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    (storageStringWriteState evm (stringViewSlot symbol) bytes).accountMap =
      if bytes.size < 32 then
        sstoreAccountMap evm.executionEnv.codeOwner
          (stringClearedAccounts evm.executionEnv.codeOwner evm.accountMap symbol
            (storageStringLength (storageStringHeader evm (stringViewSlot symbol))).toNat
            bytes.size)
          (stringViewSlot symbol) (solidityShortBytesWord bytes)
      else
        sstoreAccountMap evm.executionEnv.codeOwner
          (solidityDataWordsForwardFrom evm.executionEnv.codeOwner
            (stringClearedAccounts evm.executionEnv.codeOwner evm.accountMap symbol
              (storageStringLength (storageStringHeader evm (stringViewSlot symbol))).toNat
              bytes.size)
            (stringViewSlot symbol) bytes 0 (solidityBytesDataWordCount bytes.size))
          (stringViewSlot symbol) (solidityBytesHeaderWord bytes.size) := by
  have hp := storageStringPacked evm (stringViewSlot symbol) hvalid
  by_cases hs : bytes.size < 32 <;>
    by_cases ho : (storageStringLength (storageStringHeader evm (stringViewSlot symbol))).toNat < 32
  all_goals simp [storageStringWriteState, stringClearedAccounts, stringFirstClearedWord,
    hp, hs, ho, ↓reduceIte, decide_true, decide_false,
    storageStore_accountMap, storageStore_executionEnv,
    clearSolidityBytesDataWordsFrom_executionEnv, clearSolidityBytesDataWordsFrom_accountMap,
    writeSolidityBytesDataWordsFrom_executionEnv, writeSolidityBytesDataWordsFrom_accountMap,
    Nat.sub_zero]

theorem stringDataWrite_world (evm : State) (slot : UInt256) (bytes : ByteArray) (i n : Nat) :
    (writeSolidityBytesDataWordsFrom evm slot bytes i n).σ₀ = evm.σ₀ := by
  induction n generalizing evm i with
  | zero => rfl
  | succ n ih => simp only [writeSolidityBytesDataWordsFrom, ih, storageStore_σ₀]

theorem stringClear_world (evm : State) (slot : UInt256) (i n : Nat) :
    (clearSolidityBytesDataWordsFrom evm slot i n).σ₀ = evm.σ₀ := by
  induction n generalizing evm i with
  | zero => rfl
  | succ n ih => simp only [clearSolidityBytesDataWordsFrom, ih, storageStore_σ₀]

theorem storageStringWriteState_env (evm : State) (slot : UInt256) (bytes : ByteArray) :
    (storageStringWriteState evm slot bytes).executionEnv = evm.executionEnv := by
  unfold storageStringWriteState
  split <;> split <;> simp only [storageStore_executionEnv,
    writeSolidityBytesDataWordsFrom_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv]

theorem storageStringWriteState_world (evm : State) (slot : UInt256) (bytes : ByteArray) :
    (storageStringWriteState evm slot bytes).σ₀ = evm.σ₀ := by
  unfold storageStringWriteState
  split <;> split <;> simp only [storageStore_σ₀, stringDataWrite_world, stringClear_world]

end Benchmarks.Morpho.MetaMorphoV1_1
