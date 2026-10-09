import Benchmarks.Morpho.MorphoBlue.SafeTransferCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- GENERALIZES staticWordCallMem_read to any nonempty prefix fitting in one word.
theorem wordPrefixMem_read (prefixWord : UInt256) (ws : List UInt256)
    (mem : ByteArray) (off len : Nat) (hne : ws ≠ []) (hl : 0 < len) (hh : len ≤ 32)
    (hgap : off - mem.size < USize.size) :
    (writeCascade (writeWord mem off prefixWord) (returnWordWrites (off + len) ws)).readWithPadding
      off (len + 32 * ws.length) = prefixWord.toByteArray.extract 0 len ++ returnWordBytes ws := by
  have hs := writeWord_size mem off prefixWord hgap
  have hpos := USize.size_pos
  have hg : off + len - (writeWord mem off prefixWord).size < USize.size := by omega
  have hw : 0 < ws.length := List.length_pos_of_ne_nil hne
  have hout := writeReturnWords_size ws (writeWord mem off prefixWord) (off + len) hne hg
  rw [byteArray_readWithPadding_split_unbounded _ _ _ _ hl (by omega) (by omega)]
  rw [writeCascade_read_preserved_len _ _ _ _
    (returnWordWrites_preserveBelow ws _ _ _ _ hg (by omega) (by omega)) hl
    (by change len < 2 ^ 64; omega)]
  rw [readReturnWords ws (writeWord mem off prefixWord) (off + len) hg]
  have hp := writeWord_read_window mem off 0 len prefixWord
    (by omega) hl (by change len < 2 ^ 64; omega) hgap
  simpa only [Nat.add_zero, Nat.zero_add] using congrArg (fun bs ↦ bs ++ returnWordBytes ws) hp

end Benchmarks.Morpho.MorphoBlue
