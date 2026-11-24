import Reasoning.Listing.Sound
import Reasoning.Initcode

/-!
# Listing — code followed by arbitrary data

Creation code runs as `creationBytecode ++ tail`, the tail being the constructor arguments, and
a Vyper runtime is `template ++ suffix`, the suffix being its immutables' data section.  In both
the listed code is fixed and what follows it is arbitrary.  This file carries the listing's two
facts across the append:

* `Decodes.append`: a run of instructions that ends inside the code decodes the same with
  anything appended.
* `Checked.decodes_append`: so does every section before an offset `lim`, given the closed
  check `insideCheck` that those sections end inside the code.  (`lim` exists for one case: a
  final push cut short by the end of the code would read the appended bytes, so the section
  holding it is left out; `Checked.decodes_append_take` covers that section up to the push.)
* `Checked.jumpdest_append`: an offset where a section begins with `JUMPDEST` is a valid jump
  destination of the longer code.  (Nothing is said about destinations in the appended data.)

The two lemmas about `decode` and `D_J` under an append are `Reasoning/Initcode.lean`'s.
-/

open Ethereum Ethereum.EVM

set_option autoImplicit false

namespace Reasoning.Listing

theorem Instr.sem_fst (σ : Nat → UInt256) (i : Instr) : (i.sem σ).1 = i.opn := by
  cases i <;> rfl

/-- A run of instructions that ends inside `code` decodes the same on `code ++ tail`. -/
theorem Decodes.append {code : ByteArray} {σ : Nat → UInt256} (tail : ByteArray)
    (h64 : code.size < 2 ^ 64) : ∀ {pc : Nat} {is : List Instr},
    Decodes code σ pc is → pc + sectionWidth is ≤ code.size → Decodes (code ++ tail) σ pc is
  | _, [], _, _ => trivial
  | pc, i :: rest, h, hin => by
    have hw : i.width = 1 + argOnNBytesOfInstr (i.sem σ).1 := by rw [Instr.sem_fst]; rfl
    have hpos : pc + i.width + sectionWidth rest ≤ code.size := by
      simpa only [sectionWidth, Nat.add_assoc] using hin
    have hpc : (UInt256.ofNat pc).toNat = pc := toNat_ofNat_of_lt (by omega)
    refine ⟨?_, Decodes.append tail h64 h.tail hpos⟩
    exact Reasoning.Theory.decode_append_left_of_decode code tail (UInt256.ofNat pc)
      (i.sem σ).1 (i.sem σ).2 h.head (by rw [hpc]; omega) (by rw [hpc]; omega)

/-- The first `m` instructions of a run that decodes also decode. -/
theorem Decodes.take {code : ByteArray} {σ : Nat → UInt256} : ∀ (m : Nat) {pc : Nat}
    {is : List Instr}, Decodes code σ pc is → Decodes code σ pc (is.take m)
  | 0, _, _, _ => trivial
  | _ + 1, _, [], _ => trivial
  | m + 1, _, _ :: _, h => ⟨h.head, Decodes.take m h.tail⟩

/-- Every section before offset `lim` ends inside a code of `len` bytes. -/
def insideCheck (table : Table) (len lim : Nat) : Bool :=
  table.all fun p => decide (lim ≤ p.1) || decide (p.1 + sectionWidth p.2 ≤ len)

namespace Checked

variable {bytes : List UInt8} {table : Table}

/-- A section before `lim` decodes, at its offset, on the code followed by any `tail`. -/
theorem decodes_append (h : Checked bytes table) (σ : Nat → UInt256) (tail : ByteArray)
    {lim : Nat} (hin : insideCheck table bytes.length lim = true) (h64 : bytes.length < 2 ^ 64)
    {t : Nat} {s : Section} (hl : table.lookup t = some s) (ht : t < lim) :
    Decodes (filled bytes σ table ++ tail) σ t s := by
  have hsz := (h.scan_filled σ).2
  have hmem := List.all_eq_true.mp hin (t, s) (mem_of_lookup hl)
  have hle : t + sectionWidth s ≤ bytes.length := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hmem
    omega
  exact Decodes.append tail (by rw [hsz]; exact h64) (h.decodes_lookup σ hl) (by rw [hsz]; exact hle)

/-- The first `m` instructions of a section, when they end inside the code, decode on the code
followed by any `tail`.  For the section that holds a final push cut short by the end of the
code: everything before that push. -/
theorem decodes_append_take (h : Checked bytes table) (σ : Nat → UInt256) (tail : ByteArray)
    (h64 : bytes.length < 2 ^ 64) {t : Nat} {s : Section} (hl : table.lookup t = some s)
    (m : Nat) {len : Nat} (hlen : bytes.length = len)
    (hin : t + sectionWidth (s.take m) ≤ len) :
    Decodes (filled bytes σ table ++ tail) σ t (s.take m) := by
  have hsz := (h.scan_filled σ).2
  exact Decodes.append tail (by rw [hsz]; exact h64) (Decodes.take m (h.decodes_lookup σ hl))
    (by rw [hsz, hlen]; exact hin)

/-- An offset where a section begins with `JUMPDEST` is a valid jump destination of the code
followed by any `tail`. -/
theorem jumpdest_append (h : Checked bytes table) (σ : Nat → UInt256) (tail : ByteArray)
    {t : Nat} {s : Section} (ht : t < 2 ^ 256) (hmem : (t, s) ∈ table) (hjd : startsJD s = true) :
    (D_J (filled bytes σ table ++ tail) 0).contains (UInt256.ofNat t) = true :=
  Reasoning.Theory.D_J_contains_append_left _ tail _
    ((h.jumpdest_iff_nat σ ht).mpr ⟨s, hmem, hjd⟩)

end Checked

end Reasoning.Listing
