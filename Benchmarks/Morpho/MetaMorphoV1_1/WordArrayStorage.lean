import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayPush
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayCalldata
import Reasoning.StorageLoops

/-! Full-slot array writes and the Solidity backend's descending cleanup. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: expose an existing word list through the indexed array interface.
theorem wordArrayWords_getD (words : List UInt256) :
    wordArrayWords (fun i ↦ words[i]?.getD ⟨0⟩) 0 words.length = words := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < words.length
  · rw [wordArrayWords_getElem _ _ _ _ hi, Nat.zero_add,
      List.getElem?_eq_getElem hi, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [wordArrayWords_length]; omega),
      List.getElem?_eq_none (by omega)]

theorem wordArrayValues_getD (words : List UInt256) :
    wordArrayValues (fun i ↦ words[i]?.getD ⟨0⟩) 0 words.length =
      words.map wordBytes32Value := by
  rw [wordArrayValues, wordArrayWords_getD]

-- LIBRARY CANDIDATE: sequential full-slot writes, independent of the array's layout.
def storeWordArray (owner : AccountAddress) (σ : AccountMap) (base : UInt256)
    (words : Nat → UInt256) (index : Nat) : Nat → AccountMap
  | 0 => σ
  | n + 1 => storeWordArray owner
      (sstoreAccountMap owner σ (base + UInt256.ofNat index) (words index))
      base words (index + 1) n

theorem storageStore_asAccountUpdate (evm : State) (slot word : UInt256) :
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word =
      { evm with
        accountMap := sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap slot word } := by
  rw [← storageStore_eq_accountMap_update, storageStore_accountMap]

-- LIBRARY CANDIDATE: reverse zeroing equals forward zeroing, even if slots repeat.
theorem solidityClearWordArray {layout : StorageLayout} {er : EvaledStorageRef}
    {base : UInt256}
    (hloc : ∀ i, layout { er with steps := er.steps ++ [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (bytes32Loc (base + UInt256.ofNat i)))) (evm : State) (n : Nat) :
    solidityClearArray? layout evm er (.elem (.bytes abiBytes32Width)) n =
      .ok { evm with
        accountMap := clearDataWordsForwardFrom evm.executionEnv.codeOwner
          evm.accountMap base ⟨0⟩ n } := by
  have hl (i : Nat) : layout { er with steps := er.steps ++ [.aindex (.int (i : Int))] } =
      some (.leaf (bytes32Loc (base + UInt256.ofNat i))) := hloc i
  induction n generalizing evm with
  | zero => simp only [solidityClearArray?, clearDataWordsForwardFrom]
  | succ n ih =>
      simp only [solidityClearArray?, solidityClearStorage?, solidityLeafLoc?, hl,
        EvalResult.ofOption, bind, EvalResult.bind]
      rw [storageLocStore_bytes32 _ _ ⟨0⟩ (.int 0) rfl]
      dsimp only
      rw [ih, storageStore_asAccountUpdate]
      simp only
      rw [← sstoreZero_clearDataWordsForwardFrom_comm]
      rw [clearDataWordsForwardFrom_append]

-- LIBRARY CANDIDATE: full-slot bytes32 arrays written through a Solidity locator.
theorem solidityWriteWordArray {layout : StorageLayout} {er : EvaledStorageRef}
    {base : UInt256}
    (hloc : ∀ i, layout { er with steps := er.steps ++ [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (bytes32Loc (base + UInt256.ofNat i))))
    (evm : State) (words : Nat → UInt256) (index n : Nat) :
    solidityWriteArray? layout evm er (.elem (.bytes abiBytes32Width)) index
      (wordArrayValues words index n) =
      .ok { evm with
        accountMap := storeWordArray evm.executionEnv.codeOwner
          evm.accountMap base words index n } := by
  have hl (i : Nat) : layout { er with steps := er.steps ++ [.aindex (.int (i : Int))] } =
      some (.leaf (bytes32Loc (base + UInt256.ofNat i))) := hloc i
  induction n generalizing evm index with
  | zero => simp only [wordArrayValues, wordArrayWords, List.map_nil,
      solidityWriteArray?, storeWordArray]
  | succ n ih =>
      rw [show wordArrayValues words index (n + 1) =
        wordBytes32Value (words index) :: wordArrayValues words (index + 1) n from rfl]
      simp only [solidityWriteArray?, solidityWriteStorage?, solidityLeafLoc?, hl,
        EvalResult.ofOption, bind, EvalResult.bind]
      rw [storageLocStore_bytes32 _ _ (words index) (wordBytes32Value (words index))
        (valueToWord_bytes32_word _)]
      dsimp only
      rw [ih, storageStore_asAccountUpdate]
      rfl

-- LIBRARY CANDIDATE: exact backend order for replacing a full-slot dynamic array.
def replaceWordArraySourceAccounts (owner : AccountAddress) (σ : AccountMap)
    (header base : UInt256) (oldLength : Nat) (words : Nat → UInt256) (n : Nat) : AccountMap :=
  sstoreAccountMap owner
    (storeWordArray owner
      (sstoreAccountMap owner
        (clearDataWordsForwardFrom owner σ base ⟨0⟩ oldLength) header ⟨0⟩)
      base words 0 n) header (UInt256.ofNat n)

-- LIBRARY CANDIDATE: Solidity replacement through any full-slot array locator.
theorem solidityReplaceWordArray {layout : StorageLayout} {er : EvaledStorageRef}
    {header base : UInt256} {oldLength : Nat}
    (hloc : ∀ i, layout { er with steps := er.steps ++ [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (bytes32Loc (base + UInt256.ofNat i))))
    (hheader : solidityLengthLoc? layout er = some (uint256Loc header))
    (evm : State) (words : Nat → UInt256) (n : Nat)
    (hlen : solidityDynamicLength? layout evm er = .ok oldLength) :
    solidityWriteStorage? layout evm er (.dynamicArray (.elem (.bytes abiBytes32Width)))
      (.array (wordArrayValues words 0 n)) = .ok { evm with
        accountMap := replaceWordArraySourceAccounts evm.executionEnv.codeOwner evm.accountMap
          header base oldLength words n } := by
  rw [solidityWriteStorage?, solidityClearStorage?, hlen]
  simp only [bind, EvalResult.bind]
  rw [solidityClearWordArray hloc]
  dsimp only
  rw [hheader]
  simp only [EvalResult.ofOption]
  have hzero (s : State) : storageLocStore s (uint256Loc header) (.int 0) =
      some (Solm.EVM.storageStore s s.executionEnv.codeOwner header ⟨0⟩) :=
    storageLocStore_uint256 s header ⟨0⟩
  rw [hzero]
  dsimp only
  rw [solidityWriteWordArray hloc]
  simp only [wordArrayValues_length]
  have hstore (s : State) : storageLocStore s (uint256Loc header) (.int (n : Int)) =
      some (Solm.EVM.storageStore s s.executionEnv.codeOwner header (UInt256.ofNat n)) :=
    storageLocStore_uint256_ofNat s header n
  rw [hstore]
  dsimp only
  simp only [storageStore_asAccountUpdate]
  rfl

theorem supplyQueueElementLayout (i : Nat) :
    stringStorageLayout ⟨"supplyQueue", [.aindex (.int (Int.ofNat i))]⟩ =
      some (.leaf (bytes32Loc (solidityBytesDataBaseSlot ⟨20⟩ + UInt256.ofNat i))) := by
  change some (StorageAddr.leaf
    { slot := solidityBytesDataBaseSlot ⟨20⟩ +
        UInt256.ofNat ((keyValueToWord (.int (Int.ofNat i))).toNat / 1)
      offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat i))).toNat % 1 * 32)
      size := 32, hbound := by simp, type := .bytes ⟨31, by decide⟩ }) = _
  rw [bytes32ArrayIndexLoc]

end Benchmarks.Morpho.MetaMorphoV1_1
