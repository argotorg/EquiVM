import Reasoning.Storage

open Solm Ethereum
open Ethereum.EVM Reasoning.Theory
namespace UniswapV2Pair

-- LIBRARY CANDIDATE: storing the canonical bytes32 representation of a word.
theorem valueToWord_bytes32_word (word : UInt256) :
    valueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE word)) = some word := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size word
  simpa [valueToWord, keyValueToWord, hlen] using
    congrArg some (keyValueToWord_fixedBytes32 word)

end UniswapV2Pair
