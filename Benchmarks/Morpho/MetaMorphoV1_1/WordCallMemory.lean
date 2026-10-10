import Benchmarks.Morpho.MetaMorphoV1_1.WordPrefixMemory

/-! A selector followed by a fixed sequence of ABI words. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: static call-buffer construction with sparse, unbounded memory.
def wordCallMemory (mem : ByteArray) (ptr : Nat) (selector : UInt256)
    (words : List UInt256) : ByteArray :=
  wordSequenceMemory (writeWord mem ptr selector) (ptr + 4) words

theorem wordCallMemory_size (mem : ByteArray) (ptr : Nat) (selector : UInt256)
    {words : List UInt256} (hne : words ≠ []) :
    (wordCallMemory mem ptr selector words).size = max mem.size (ptr + 4 + 32 * words.length) :=
  wordPrefixMemory_size mem ptr selector (by decide) hne

theorem wordCallMemory_read (mem : ByteArray) (ptr : Nat) (selector : UInt256)
    (words : List UInt256) :
    (wordCallMemory mem ptr selector words).readWithPadding ptr (4 + 32 * words.length) =
      selector.toByteArray.extract 0 4 ++ wordBytes words :=
  wordPrefixMemory_read mem ptr selector (by decide) (by decide) words

theorem wordCallMemory_prefix (mem : ByteArray) (ptr : Nat) (selector : UInt256)
    (words : List UInt256) : MemoryPrefix mem (wordCallMemory mem ptr selector words) ptr :=
  wordPrefixMemory_prefix mem ptr selector 4 words

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
