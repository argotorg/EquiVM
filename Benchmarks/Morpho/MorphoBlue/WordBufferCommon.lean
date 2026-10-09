import Benchmarks.Morpho.MorphoBlue.ReturnCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: contiguous word buffers may replace an existing memory region.
theorem returnWordWrites_preserveBelow (ws : List UInt256) (size off read len : Nat)
    (hgap : off - size < USize.size) (hin : read + len ≤ size) (hlo : read + len ≤ off) :
    WindowDisjointFromWrites size read len (returnWordWrites off ws) := by
  induction ws generalizing size off with
  | nil => trivial
  | cons w ws ih =>
    refine ⟨hgap, Or.inl ⟨hlo, hin⟩, ih _ _ ?_ (by omega) (by omega)⟩
    have hpos := USize.size_pos
    omega

theorem writeReturnWords_size (ws : List UInt256) (mem : ByteArray) (off : Nat)
    (hne : ws ≠ []) (hgap : off - mem.size < USize.size) :
    (writeCascade mem (returnWordWrites off ws)).size = max mem.size (off + 32 * ws.length) := by
  induction ws generalizing mem off with
  | nil => exact (hne rfl).elim
  | cons w ws ih =>
    have hs := writeWord_size mem off w hgap
    simp only [returnWordWrites, writeCascade_cons]
    by_cases he : ws = []
    · subst ws
      simpa only [returnWordWrites, writeCascade_nil, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.mul_one] using hs
    · rw [ih _ _ he (by rw [hs]; have hpos := USize.size_pos; omega)]
      rw [hs]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem readReturnWords (ws : List UInt256) (mem : ByteArray) (off : Nat)
    (hgap : off - mem.size < USize.size) :
    (writeCascade mem (returnWordWrites off ws)).readWithPadding off (32 * ws.length) =
      returnWordBytes ws := by
  induction ws generalizing mem off with
  | nil => simp only [returnWordWrites, writeCascade_nil, List.length_nil, Nat.mul_zero,
      byteArray_readWithPadding_zero, returnWordBytes]
  | cons w ws ih =>
    have hs := writeWord_size mem off w hgap
    have hg : off + 32 - (writeWord mem off w).size < USize.size := by
      rw [hs]; have hpos := USize.size_pos; omega
    have hfirst := writeCascade_read_word_of_head mem off w
      (returnWordWrites (off + 32) ws) hgap
      (returnWordWrites_preserveBelow ws _ _ _ _ (by have hpos := USize.size_pos; omega)
        (by omega) (by omega))
    by_cases he : ws = []
    · subst ws
      simpa only [returnWordWrites, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.mul_one, returnWordBytes, ByteArray.append_empty] using hfirst
    · have hlen : 0 < 32 * ws.length := by
        have : 0 < ws.length := List.length_pos_of_ne_nil he
        omega
      have hout := writeReturnWords_size (w :: ws) mem off (by simp) hgap
      simp only [List.length_cons] at hout
      rw [show 32 * (w :: ws).length = 32 + 32 * ws.length by simp; omega]
      rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by omega) hlen (by omega)]
      rw [show returnWordWrites off (w :: ws) =
        (off, w) :: returnWordWrites (off + 32) ws from rfl, hfirst]
      change _ ++ (writeCascade (writeWord mem off w) (returnWordWrites (off + 32) ws)).readWithPadding
        (off + 32) (32 * ws.length) = _
      rw [ih _ _ hg]
      rfl

def staticWordCallMem (selector : UInt256) (words : List UInt256)
    (mem : ByteArray) (off : Nat) : ByteArray :=
  writeCascade (writeWord mem off selector) (returnWordWrites (off + 4) words)

-- LIBRARY CANDIDATE: a four-byte selector followed by a static word argument buffer.
theorem staticWordCallMem_read (selector : UInt256) (words : List UInt256)
    (mem : ByteArray) (off : Nat) (hne : words ≠ [])
    (hgap : off - mem.size < USize.size) :
    (staticWordCallMem selector words mem off).readWithPadding off (4 + 32 * words.length) =
      selector.toByteArray.extract 0 4 ++ returnWordBytes words := by
  have hs := writeWord_size mem off selector hgap
  have hpos := USize.size_pos
  have hg : off + 4 - (writeWord mem off selector).size < USize.size := by omega
  have hlen : 0 < words.length := List.length_pos_of_ne_nil hne
  have hout := writeReturnWords_size words (writeWord mem off selector) (off + 4) hne hg
  unfold staticWordCallMem
  rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by omega) (by omega) (by omega)]
  rw [writeCascade_read_preserved_len _ _ _ _
    (returnWordWrites_preserveBelow words _ _ _ _ hg (by omega) (by omega))
    (by omega) (by norm_num)]
  rw [readReturnWords words (writeWord mem off selector) (off + 4) hg]
  have hselector := writeWord_read_window mem off 0 4 selector
    (by omega) (by omega) (by norm_num) hgap
  simpa only [Nat.add_zero] using congrArg (fun bs ↦ bs ++ returnWordBytes words) hselector

theorem returnWordBytes_append (xs ys : List UInt256) :
    returnWordBytes (xs ++ ys) = returnWordBytes xs ++ returnWordBytes ys := by
  induction xs with
  | nil => simp only [List.nil_append, returnWordBytes, ByteArray.empty_append]
  | cons w ws ih =>
    simp only [List.cons_append, returnWordBytes, ih, ByteArray.append_assoc]

end Benchmarks.Morpho.MorphoBlue
