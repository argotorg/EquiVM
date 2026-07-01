import Examples.BytesStoreLite.Bytecode
import Reasoning.Dispatch

/-!
# BytesStoreLite — full-contract Solm dispatch facts

These lemmas connect the full `BytesStoreLite` specification's transition order with the 15
keccak selector axioms in `Bytecode.lean`.  They are reusable proof plumbing for the optimized
full-contract equivalence target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace BytesStoreLite

theorem bytesStoreLiteTransitions :
    bytesStoreLiteContract.transitions = [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter] :=
  rfl

/-- Function selectors in `bytesStoreLiteContract.transitions` order. -/
def bytesStoreLiteSelBytes : Nat -> ByteArray
  | 0 => ⟨#[0x03, 0x99, 0x32, 0x1e]⟩
  | 1 => ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩
  | 2 => ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩
  | 3 => ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩
  | 4 => ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩
  | 5 => ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩
  | 6 => ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩
  | 7 => ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩
  | 8 => ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩
  | 9 => ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩
  | 10 => ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩
  | 11 => ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩
  | 12 => ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩
  | 13 => ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩
  | _ => ⟨#[0x39, 0x1d, 0x72, 0x80]⟩

/-- `ByteArray` `==` reflects equality. -/
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)


theorem bytesStoreLiteDispatch_set {cd : ByteArray}
    (hsel : (⟨#[0x03, 0x99, 0x32, 0x1e]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [])
    (post := [setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := setTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
  · rw [selectorOf, setBytesSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_setByte {cd : ByteArray}
    (hsel : (⟨#[0x1c, 0x52, 0x47, 0x7d]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setByteTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition])
    (post := [clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := setByteTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, setByteSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_clearCurrent {cd : ByteArray}
    (hsel : (⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some clearCurrentTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition])
    (post := [currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := clearCurrentTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, clearCurrentSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_currentLength {cd : ByteArray}
    (hsel : (⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some currentLengthGetter := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition])
    (post := [pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := currentLengthGetter)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, currentLengthSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_pushChunk {cd : ByteArray}
    (hsel : (⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some pushChunkTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter])
    (post := [setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := pushChunkTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, pushChunkSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_setChunk {cd : ByteArray}
    (hsel : (⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setChunkTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition])
    (post := [setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := setChunkTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, setChunkSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_setChunkByte {cd : ByteArray}
    (hsel : (⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setChunkByteTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition])
    (post := [chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := setChunkByteTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, setChunkByteSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_chunkLength {cd : ByteArray}
    (hsel : (⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some chunkLengthGetter := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition])
    (post := [setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := chunkLengthGetter)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, chunkLengthSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_setPacket {cd : ByteArray}
    (hsel : (⟨#[0x14, 0xf1, 0x7c, 0x69]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setPacketTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter])
    (post := [setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := setPacketTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, setPacketSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_setPacketByte {cd : ByteArray}
    (hsel : (⟨#[0x0a, 0xb2, 0x59, 0x00]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setPacketByteTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition])
    (post := [packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := setPacketByteTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, setPacketByteSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_packetLength {cd : ByteArray}
    (hsel : (⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some packetLengthGetter := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition])
    (post := [packetTagGetter, setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := packetLengthGetter)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, packetLengthSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_packetTag {cd : ByteArray}
    (hsel : (⟨#[0x99, 0x3e, 0x0a, 0x90]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some packetTagGetter := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter])
    (post := [setMappedTransition, setMappedByteTransition, mappedLengthGetter])
    (ti := packetTagGetter)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, packetLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, packetTagSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_setMapped {cd : ByteArray}
    (hsel : (⟨#[0xe1, 0x91, 0x9b, 0x17]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setMappedTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter])
    (post := [setMappedByteTransition, mappedLengthGetter])
    (ti := setMappedTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, packetLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, packetTagSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, setMappedSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_setMappedByte {cd : ByteArray}
    (hsel : (⟨#[0x13, 0x2f, 0xa3, 0x46]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some setMappedByteTransition := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition])
    (post := [mappedLengthGetter])
    (ti := setMappedByteTransition)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, packetLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, packetTagSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setMappedSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, setMappedByteSelectorBytes]
    exact hsel
theorem bytesStoreLiteDispatch_mappedLength {cd : ByteArray}
    (hsel : (⟨#[0x39, 0x1d, 0x72, 0x80]⟩ == cd.extract 0 4) = true) :
    dispatchMsg bytesStoreLiteContract cd = some mappedLengthGetter := by
  refine dispatchMsg_eq_some_of_split
    (contract := bytesStoreLiteContract)
    (pre := [setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter, pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter, setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter, setMappedTransition, setMappedByteTransition])
    (post := [])
    (ti := mappedLengthGetter)
    (cd := cd) bytesStoreLiteTransitions ?_ ?_
  · intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setPacketByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, packetLengthSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, packetTagSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setMappedSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
    · subst t
      rw [selectorOf, setMappedByteSelectorBytes]
      have hcd := (byteArray_eq_of_beq hsel).symm
      rw [hcd]
      decide
  · rw [selectorOf, mappedLengthSelectorBytes]
    exact hsel

theorem bytesStoreLiteDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg bytesStoreLiteContract cd = none := by
  rw [dispatchMsg_eq_dispatchList, bytesStoreLiteTransitions]
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
    · subst t
      rw [selectorOf, setBytesSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, setByteSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, clearCurrentSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, currentLengthSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, pushChunkSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, setChunkSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, setChunkByteSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, chunkLengthSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, setPacketSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, setPacketByteSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, packetLengthSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, packetTagSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, setMappedSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, setMappedByteSelectorBytes]
      rfl
    · subst t
      rw [selectorOf, mappedLengthSelectorBytes]
      rfl) h

theorem bytesStoreLiteDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 15 → (bytesStoreLiteSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg bytesStoreLiteContract cd = none := by
  rw [dispatchMsg_eq_dispatchList, bytesStoreLiteTransitions]
  apply dispatchList_none_of_all_ne
  intro t ht
  simp at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht
  · subst t
    rw [selectorOf, setBytesSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 0 (by omega)
  · subst t
    rw [selectorOf, setByteSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 1 (by omega)
  · subst t
    rw [selectorOf, clearCurrentSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 2 (by omega)
  · subst t
    rw [selectorOf, currentLengthSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 3 (by omega)
  · subst t
    rw [selectorOf, pushChunkSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 4 (by omega)
  · subst t
    rw [selectorOf, setChunkSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 5 (by omega)
  · subst t
    rw [selectorOf, setChunkByteSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 6 (by omega)
  · subst t
    rw [selectorOf, chunkLengthSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 7 (by omega)
  · subst t
    rw [selectorOf, setPacketSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 8 (by omega)
  · subst t
    rw [selectorOf, setPacketByteSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 9 (by omega)
  · subst t
    rw [selectorOf, packetLengthSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 10 (by omega)
  · subst t
    rw [selectorOf, packetTagSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 11 (by omega)
  · subst t
    rw [selectorOf, setMappedSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 12 (by omega)
  · subst t
    rw [selectorOf, setMappedByteSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 13 (by omega)
  · subst t
    rw [selectorOf, mappedLengthSelectorBytes]
    simpa [bytesStoreLiteSelBytes] using hnm 14 (by omega)

end BytesStoreLite
