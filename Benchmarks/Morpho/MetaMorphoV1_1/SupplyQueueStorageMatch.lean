import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStorageSource
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayStorageAlgebra

/-! Concrete slot bounds and equality of source and runtime queue replacement. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem supplyQueueDataBase_eq : solidityBytesDataBaseSlot ⟨20⟩ = UInt256.ofNat
    93369884277498597659590946175997448338802118867485977633968544981113634346220 := by
  native_decide

theorem supplyQueueDataBase_bounds :
    20 < (solidityBytesDataBaseSlot ⟨20⟩).toNat ∧
      (solidityBytesDataBaseSlot ⟨20⟩).toNat + 2 ^ 251 < UInt256.size := by
  rw [supplyQueueDataBase_eq]
  decide

theorem supplyQueueDataSlot_ne_header {i : Nat} (hi : i < 2 ^ 251) :
    (⟨20⟩ : UInt256) ≠ solidityBytesDataBaseSlot ⟨20⟩ + UInt256.ofNat i := by
  intro he
  have hb := supplyQueueDataBase_bounds
  have hn := congrArg UInt256.toNat he
  rw [uadd_word_ofNat_toNat _ _ (by omega)] at hn
  change 20 = _ at hn
  omega

def supplyQueueRuntimeAccounts (owner : AccountAddress) (σ : AccountMap)
    (oldLength : Nat) (words : Nat → UInt256) (n : Nat) : AccountMap :=
  storeWordArray owner
    (clearDataWordsForwardFrom owner (sstoreAccountMap owner σ ⟨20⟩ (UInt256.ofNat n))
      (solidityBytesDataBaseSlot ⟨20⟩ + UInt256.ofNat n) ⟨0⟩ (oldLength - n))
    (solidityBytesDataBaseSlot ⟨20⟩) words 0 n

theorem supplyQueueAccounts_match (owner : AccountAddress) (σ : AccountMap)
    (words : Nat → UInt256) (oldLength n : Nat)
    (hold : oldLength < 2 ^ 251) (hnew : n < 2 ^ 251) :
    supplyQueueSourceAccounts owner σ oldLength words n =
      supplyQueueRuntimeAccounts owner σ oldLength words n := by
  exact replaceWordArrayAccounts_match owner σ ⟨20⟩ (solidityBytesDataBaseSlot ⟨20⟩)
    words oldLength n
    (fun j hj ↦ supplyQueueDataSlot_ne_header (by omega))
    (fun j hj ↦ supplyQueueDataSlot_ne_header (by omega))

end Benchmarks.Morpho.MetaMorphoV1_1
