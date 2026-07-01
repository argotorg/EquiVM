import Examples.BytesStoreLite.Spec

/-!
# BytesStoreLite storage-layout facts

This file is the explicit trusted boundary for symbolic keccak storage separation facts.  These are
layout assumptions, not equivalence proof shortcuts: they state that Solidity's keccak-derived
dynamic-data regions do not alias their headers or unrelated static slots.
-/

open Solm ABI Ethereum

namespace BytesStoreLite

/-- Trusted Solidity storage-layout disjointness: long `bytes` data words do not alias their
header slot. -/
axiom bytesLikeDataWordSlot_ne_base (baseSlot wordIndex : Ethereum.UInt256) :
    bytesLikeDataBase baseSlot + wordIndex ≠ baseSlot

theorem bytesLikeDataSlot_ne_base (baseSlot idx : Ethereum.UInt256) :
    bytesLikeDataBase baseSlot + Ethereum.UInt256.div idx ⟨32⟩ ≠ baseSlot :=
  bytesLikeDataWordSlot_ne_base baseSlot (Ethereum.UInt256.div idx ⟨32⟩)

theorem bytesStoreLiteChunksElemSlot_ne_length (oldLen : Ethereum.UInt256) :
    chunksDataBase + oldLen ≠ (⟨1⟩ : Ethereum.UInt256) := by
  simpa [chunksDataBase] using
    bytesLikeDataWordSlot_ne_base (⟨1⟩ : Ethereum.UInt256) oldLen

/-- Trusted Solidity storage-layout disjointness: data words of `chunks[i]` do not alias the
`chunks.length` slot. -/
axiom bytesStoreLiteChunkDataWordSlot_ne_length
    (chunkIndex wordIndex : Ethereum.UInt256) :
    bytesLikeDataBase (chunksDataBase + chunkIndex) + wordIndex ≠
      (⟨1⟩ : Ethereum.UInt256)

end BytesStoreLite
