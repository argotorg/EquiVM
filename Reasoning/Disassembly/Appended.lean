import EVM.Disassembly.Sound
import Reasoning.Initcode

/-!
# Code followed by other data

Creation code runs as `creationBytecode ++ args`, and a Vyper runtime is its template followed by
its immutables. This file shows that the sections still decode, and that their `JUMPDEST`s stay
valid, when arbitrary bytes are appended to the code.

The exception is a push at the very end of the code that is missing some of its immediate bytes,
because it would read them from the appended data. The theorems therefore only cover the
sections before an offset `lim`, and `Checked.decodes_appended_take` covers the instructions that
come before such a push.
-/

open Ethereum Ethereum.EVM EVM.Disassembly

set_option autoImplicit false

namespace Reasoning.Disassembly

theorem Instr.sem_fst (σ : Nat → UInt256) (i : Instr) : (i.sem σ).1 = i.opn := by
  cases i <;> rfl

/-- Instructions that end inside `code` decode the same in `code ++ tail`. -/
theorem DecodesFrom.appended {code : ByteArray} {σ : Nat → UInt256} (tail : ByteArray)
    (h64 : code.size < 2 ^ 64) : ∀ {pc : Nat} {is : List Instr},
    DecodesFrom code σ pc is → pc + sectionWidth is ≤ code.size → DecodesFrom (code ++ tail) σ pc is
  | _, [], _, _ => trivial
  | pc, i :: rest, h, hin => by
    have hw : i.width = 1 + argOnNBytesOfInstr (i.sem σ).1 := by rw [Instr.sem_fst]; rfl
    have hpos : pc + i.width + sectionWidth rest ≤ code.size := by
      simpa only [sectionWidth, Nat.add_assoc] using hin
    have hpc : (UInt256.ofNat pc).toNat = pc :=
      UInt256.toNat_ofNat_of_lt (by unfold UInt256.size; omega)
    refine ⟨?_, DecodesFrom.appended tail h64 h.tail hpos⟩
    exact Reasoning.Theory.decode_append_left_of_decode code tail (UInt256.ofNat pc)
      (i.sem σ).1 (i.sem σ).2 h.head (by rw [hpc]; omega) (by rw [hpc]; omega)

/-- A prefix of instructions that decode also decodes. -/
theorem DecodesFrom.take {code : ByteArray} {σ : Nat → UInt256} : ∀ (m : Nat) {pc : Nat}
    {is : List Instr}, DecodesFrom code σ pc is → DecodesFrom code σ pc (is.take m)
  | 0, _, _, _ => trivial
  | _ + 1, _, [], _ => trivial
  | m + 1, _, _ :: _, h => ⟨h.head, DecodesFrom.take m h.tail⟩

/-- The offset of the first section that does not end inside a code of `len` bytes, or `len + 1` if
every section does. Bytecode files use it as their `lim`. -/
def limOf (table : List (Nat × List Instr)) (len : Nat) : Nat :=
  ((table.find? fun p => p.1 + sectionWidth p.2 > len).map (·.1)).getD (len + 1)

/-- The number of complete instructions in the section at `lim`, i.e. those before the truncated
push. -/
def lastCount (table : List (Nat × List Instr)) (lim : Nat) : Nat :=
  ((table.lookup lim).map (·.length - 1)).getD 0

/-- Every section before `lim` ends inside a code of `len` bytes. -/
def insideCheck (table : List (Nat × List Instr)) (len lim : Nat) : Bool :=
  table.all fun p => decide (lim ≤ p.1) || decide (p.1 + sectionWidth p.2 ≤ len)

namespace Checked

variable {bytes : List UInt8} {table : List (Nat × List Instr)}

/-- A section before `lim` decodes in the code followed by any `tail`. -/
theorem decodes_appended (h : Checked bytes table) (σ : Nat → UInt256) (tail : ByteArray)
    {lim : Nat} (hin : insideCheck table bytes.length lim = true) (h64 : bytes.length < 2 ^ 64)
    {t : Nat} {s : List Instr} (hl : table.lookup t = some s) (ht : t < lim) :
    DecodesFrom (filled bytes σ table ++ tail) σ t s := by
  have hsz := (h.scan_filled σ).2
  have hmem := List.all_eq_true.mp hin (t, s) (mem_of_lookup hl)
  have hle : t + sectionWidth s ≤ bytes.length := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hmem
    omega
  exact DecodesFrom.appended tail (by rw [hsz]; exact h64) (h.decodes_lookup σ hl)
    (by rw [hsz]; exact hle)

/-- The first `m` instructions of a section decode in the code followed by any `tail`, if they end
inside the code. -/
theorem decodes_appended_take (h : Checked bytes table) (σ : Nat → UInt256) (tail : ByteArray)
    (h64 : bytes.length < 2 ^ 64) {t : Nat} {s : List Instr} (hl : table.lookup t = some s)
    (m : Nat) {len : Nat} (hlen : bytes.length = len)
    (hin : t + sectionWidth (s.take m) ≤ len) :
    DecodesFrom (filled bytes σ table ++ tail) σ t (s.take m) := by
  have hsz := (h.scan_filled σ).2
  exact DecodesFrom.appended tail (by rw [hsz]; exact h64) (DecodesFrom.take m (h.decodes_lookup σ hl))
    (by rw [hsz, hlen]; exact hin)

/-- The offset of a section that starts with a `JUMPDEST` is a valid jump destination of the code
followed by any `tail`. -/
theorem jumpdest_appended (h : Checked bytes table) (σ : Nat → UInt256) (tail : ByteArray)
    {t : Nat} {s : List Instr} (ht : t < 2 ^ 256) (hmem : (t, s) ∈ table) (hjd : startsJD s = true) :
    (D_J (filled bytes σ table ++ tail) 0).contains (UInt256.ofNat t) = true :=
  Reasoning.Theory.D_J_contains_append_left _ tail _
    ((h.jumpdest_iff_nat σ ht).mpr ⟨s, hmem, hjd⟩)

end Checked

end Reasoning.Disassembly
