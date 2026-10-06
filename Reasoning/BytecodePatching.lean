import Reasoning.Initcode
import Reasoning.Memory
import Solm.Immutables

/-!
# Bytecode patching

Splicing immutable values into bytecode preserves bytes, decoded instructions, and jump
destinations outside the patched windows.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

set_option autoImplicit false

/-- A `Value`'s 32-byte word (big-endian), as `valueToWord` computes it. -/
def wordBytes? (v : Value) : Option ByteArray :=
  (valueToWord v).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def PatchesStartAt (n : Nat) (ps : List (Nat × ByteArray)) : Prop :=
  ∀ p ∈ ps, n ≤ p.1

def PatchWindowDisjoint (lo hi : Nat) (p : Nat × ByteArray) : Prop :=
  p.1 + p.2.size ≤ lo ∨ hi ≤ p.1

def PatchWindowDisjoint32 (lo hi : Nat) (p : Nat × ByteArray) : Prop :=
  p.1 + 32 ≤ lo ∨ hi ≤ p.1

def PatchesWindowDisjoint32 (lo hi : Nat) (ps : List (Nat × ByteArray)) : Prop :=
  ∀ p ∈ ps, PatchWindowDisjoint32 lo hi p

def patchOffsetDisjoint32Bool (lo hi off : Nat) : Bool :=
  decide (off + 32 ≤ lo) || decide (hi ≤ off)

def patchOffsetsWindowDisjoint32Bool (lo hi : Nat) : List Nat → Bool
  | [] => true
  | off :: offs =>
      patchOffsetDisjoint32Bool lo hi off && patchOffsetsWindowDisjoint32Bool lo hi offs

theorem patchWindowDisjoint32_of_offset_bool {lo hi : Nat} {p : Nat × ByteArray}
    (h : patchOffsetDisjoint32Bool lo hi p.1 = true) :
    PatchWindowDisjoint32 lo hi p := by
  simp [patchOffsetDisjoint32Bool] at h
  exact h

theorem patchesWindowDisjoint32_of_offsets_bool {lo hi : Nat} {ps : List (Nat × ByteArray)}
    (h : patchOffsetsWindowDisjoint32Bool lo hi (ps.map Prod.fst) = true) :
    PatchesWindowDisjoint32 lo hi ps := by
  induction ps with
  | nil =>
      intro p hp
      cases hp
  | cons p ps ih =>
      simp [patchOffsetsWindowDisjoint32Bool] at h
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact patchWindowDisjoint32_of_offset_bool h.1
      · exact ih h.2 q hq

def patchScanReaches (fuel : Nat) (template : ByteArray) (offs : List Nat)
    (i target : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      match template.get? i >>= parseInstr with
      | none => false
      | some op =>
          patchOffsetsWindowDisjoint32Bool i (i + 1) offs &&
            if i = target ∧ op = .JUMPDEST then
              true
            else
              patchScanReaches fuel template offs (N i op) target

theorem byteArray_get?_extract_prefix (b : ByteArray) {n i : Nat}
    (hi : i < n) (hn : n ≤ b.size) :
    (b.extract 0 n).get? i = b.get? i := by
  unfold ByteArray.get?
  have hleft : i < (b.extract 0 n).size := by
    rw [ByteArray.size_extract]
    omega
  have hright : i < b.size := by omega
  simp only [dif_pos hleft, dif_pos hright]
  apply congrArg some
  change (b.extract 0 n)[i] = b[i]
  simp only [ByteArray.get_extract, Nat.zero_add]

theorem spliceBytes_get?_left {template value out : ByteArray} {off i : Nat}
    (hsp : spliceBytes? template off value = some out) (hi : i < off) :
    out.get? i = template.get? i := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    rw [Reasoning.Theory.byteArray_get?_append_left (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size)]
    · rw [Reasoning.Theory.byteArray_get?_append_left (template.extract 0 off) value]
      · exact byteArray_get?_extract_prefix template hi (by omega)
      · rw [ByteArray.size_extract]
        omega
    · rw [ByteArray.size_append, ByteArray.size_extract]
      omega
  · cases hsp

theorem spliceBytes_extract_left {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out) (hj : j ≤ off) :
    out.extract i j = template.extract i j := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    rw [Reasoning.Theory.extract_append_left (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) i j]
    · rw [Reasoning.Theory.extract_append_left (template.extract 0 off) value i j]
      · exact Reasoning.Theory.extract_prefix template off i j hj
      · rw [ByteArray.size_extract]
        omega
    · rw [ByteArray.size_append, ByteArray.size_extract]
      omega
  · cases hsp

theorem spliceBytes_extract'_left {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64) (hj : j ≤ off) :
    out.extract' i j = template.extract' i j := by
  unfold ByteArray.extract'
  have hguard : (decide (i < 2 ^ 64) && decide (j < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact spliceBytes_extract_left hsp hj

theorem spliceBytes_extract_middle {template value out : ByteArray} {off : Nat}
    (hsp : spliceBytes? template off value = some out) :
    out.extract off (off + value.size) = value := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    have hprefix : (template.extract 0 off).size = off := by
      rw [ByteArray.size_extract]
      omega
    rw [Reasoning.Theory.extract_append_left (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) off (off + value.size)]
    · rw [Reasoning.Theory.extract_append_right' (template.extract 0 off) value off
        (off + value.size) (by rw [hprefix]) (by rw [hprefix])]
    · rw [ByteArray.size_append, hprefix]
  · cases hsp

theorem patchRuntime_get?_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n i : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (hi : i < n) :
    out.get? i = template.get? i := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp : n ≤ p.1 := hps p (by simp)
      have hrest : PatchesStartAt n ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            calc
              out.get? i = mid.get? i := ih hpatch hrest
              _ = template.get? i := spliceBytes_get?_left hsp (by omega)
      · rw [if_neg hsz] at hpatch
        simp at hpatch

theorem patchRuntime_extract_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n i j : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (hj : j ≤ n) :
    out.extract i j = template.extract i j := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp : n ≤ p.1 := hps p (by simp)
      have hrest : PatchesStartAt n ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            calc
              out.extract i j = mid.extract i j := ih hpatch hrest
              _ = template.extract i j := spliceBytes_extract_left hsp (le_trans hj hp)
      · rw [if_neg hsz] at hpatch
        simp at hpatch

theorem patchRuntime_extract'_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n i j : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64)
    (hj : j ≤ n) :
    out.extract' i j = template.extract' i j := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp : n ≤ p.1 := hps p (by simp)
      have hrest : PatchesStartAt n ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            calc
              out.extract' i j = mid.extract' i j := ih hpatch hrest
              _ = template.extract' i j :=
                spliceBytes_extract'_left hsp hi64 hj64 (le_trans hj hp)
      · rw [if_neg hsz] at hpatch
        simp at hpatch

theorem patchRuntime_decode_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (pc : UInt256) (hwin : pc.toNat + 33 ≤ n)
    (hn64 : n < 2 ^ 64) :
    decode out pc = decode template pc := by
  unfold decode
  rw [patchRuntime_get?_left hpatch hps (by omega : pc.toNat < n)]
  cases hget : template.get? pc.toNat with
  | none => rfl
  | some byte =>
      cases hinstr : parseInstr byte with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            have hargle := argOnNBytesOfInstr_le_32 instr
            have hi64 : pc.toNat + 1 < 2 ^ 64 := by omega
            have hj64 : pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by omega
            have hjn : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n := by omega
            rw [patchRuntime_extract'_left (n := n) hpatch hps hi64 hj64 hjn]

theorem patchRuntime_decode_left_precise {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {n : Nat}
    (hpatch : patchRuntime template ps = some out) (hps : PatchesStartAt n ps)
    (pc : UInt256) (hpc : pc.toNat < n)
    (hwin : ∀ byte instr, template.get? pc.toNat = some byte →
      parseInstr byte = some instr → pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n)
    (hn64 : n < 2 ^ 64) :
    decode out pc = decode template pc := by
  unfold decode
  rw [patchRuntime_get?_left hpatch hps hpc]
  cases hget : template.get? pc.toNat with
  | none => rfl
  | some byte =>
      cases hinstr : parseInstr byte with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            have hi64 : pc.toNat + 1 < 2 ^ 64 := by omega
            have hj64 : pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by
              have := hwin byte instr hget hinstr
              omega
            have hjn : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n :=
              hwin byte instr hget hinstr
            rw [patchRuntime_extract'_left (n := n) hpatch hps hi64 hj64 hjn]

theorem patchRuntime_decode_left_of_decode {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {n : Nat}
    (hpatch : patchRuntime template ps = some out) (hps : PatchesStartAt n ps)
    (pc : UInt256) (res : Operation × Option (UInt256 × Nat))
    (hdec : decode template pc = some res) (hpc : pc.toNat < n)
    (hwin : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ n)
    (hn64 : n < 2 ^ 64) :
    decode out pc = some res := by
  unfold decode at hdec ⊢
  rw [patchRuntime_get?_left hpatch hps hpc]
  cases hget : template.get? pc.toNat with
  | none => simp [hget] at hdec
  | some byte =>
      simp [hget] at hdec
      cases hinstr : parseInstr byte with
      | none => simp [hinstr] at hdec
      | some instr =>
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [hinstr, harg] at hdec ⊢
            exact hdec
          · simp [hinstr, harg] at hdec
            cases hdec
            have hjn : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n := by
              simpa using hwin
            have hi64 : pc.toNat + 1 < 2 ^ 64 := by omega
            have hj64 : pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by omega
            simp [hinstr, harg]
            rw [patchRuntime_extract'_left (n := n) hpatch hps hi64 hj64 hjn]

@[simp] theorem wordBytes_address (a : EVM.Address) :
    wordBytes? (.address a) = some { data := (EVM.Word.ofNat ↑a).toBytesBE.toArray } := by
  rfl

theorem uInt256OfByteArray_word_toBytesBE (w : UInt256) :
    uInt256OfByteArray ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray) = w := by
  apply word_toBytesBE_inj
  rw [toBytesBE_uInt256OfByteArray_of_size]
  · rw [byteArray_toList_eq]
  · simpa using word_toBytesBE_toByteArray_size w

theorem decode_push32_of_get?_extract' {code : ByteArray} {pc w : UInt256}
    (hget : code.get? pc.toNat = some 0x7f)
    (hpayload : code.extract' (pc.toNat + 1) (pc.toNat + 33)
        = ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray)) :
    decode code pc = some (.Push .PUSH32, some (w, 32)) := by
  unfold decode
  rw [hget]
  have hparse : parseInstr 0x7f = some (.Push .PUSH32) := by decide
  simp [hparse, argOnNBytesOfInstr]
  rw [show pc.toNat + 1 + 32 = pc.toNat + 33 by omega]
  rw [hpayload]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem byteArray_eq_extract_prefix_suffix (b : ByteArray) (n : Nat) (hn : n ≤ b.size) :
    b = b.extract 0 n ++ b.extract n b.size := by
  calc
    b = b.extract 0 b.size := (Reasoning.Theory.byteArray_extract_self b).symm
    _ = b.extract 0 n ++ b.extract n b.size :=
      ByteArray.extract_eq_extract_append_extract (a := b) (i := 0) (k := b.size)
        n (Nat.zero_le _) hn

theorem byteArray_get?_append_right (A B : ByteArray) {i : Nat} (h : A.size ≤ i) :
    (A ++ B).get? i = B.get? (i - A.size) := by
  unfold ByteArray.get?
  by_cases hab : i < (A ++ B).size
  · have hb : i - A.size < B.size := by
      rw [ByteArray.size_append] at hab
      omega
    simp only [dif_pos hab, dif_pos hb]
    apply congrArg some
    change (A ++ B)[i] = B[i - A.size]
    rw [ByteArray.get_append_right h]
  · have hb : ¬ i - A.size < B.size := by
      rw [ByteArray.size_append] at hab
      omega
    simp only [dif_neg hab, dif_neg hb]

theorem spliceBytes_get?_right {template value out : ByteArray} {off i : Nat}
    (hsp : spliceBytes? template off value = some out) (hi : off + value.size ≤ i) :
    out.get? i = template.get? i := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    have hprefix : (template.extract 0 off ++ value).size = off + value.size := by
      rw [ByteArray.size_append, ByteArray.size_extract]
      omega
    rw [byteArray_get?_append_right (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) (by omega)]
    unfold ByteArray.get?
    by_cases hsuf : i - (template.extract 0 off ++ value).size <
        (template.extract (off + value.size) template.size).size
    · have htemp : i < template.size := by
        rw [hprefix, ByteArray.size_extract] at hsuf
        omega
      simp only [dif_pos hsuf, dif_pos htemp]
      apply congrArg some
      let suffix := template.extract (off + value.size) template.size
      change suffix[i - (template.extract 0 off ++ value).size] = template[i]
      rw [ByteArray.get_extract hsuf]
      have hoff : min off template.size = off := by omega
      have hidx : off + value.size + (i - (off + value.size)) = i := by omega
      simp [hoff, hidx]
    · have htemp : ¬ i < template.size := by
        rw [hprefix, ByteArray.size_extract] at hsuf
        omega
      simp only [dif_neg hsuf, dif_neg htemp]
  · cases hsp

theorem spliceBytes_extract_right {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out) (hi : off + value.size ≤ i) :
    out.extract i j = template.extract i j := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    have hprefix : (template.extract 0 off ++ value).size = off + value.size := by
      rw [ByteArray.size_append, ByteArray.size_extract]
      omega
    have htprefix : (template.extract 0 (off + value.size)).size = off + value.size := by
      rw [ByteArray.size_extract]
      omega
    have hsplit := byteArray_eq_extract_prefix_suffix template (off + value.size) hle
    conv_rhs => rw [hsplit]
    rw [Reasoning.Theory.extract_append_right_window (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) i j (by omega)]
    rw [Reasoning.Theory.extract_append_right_window (template.extract 0 (off + value.size))
      (template.extract (off + value.size) template.size) i j (by omega)]
    rw [hprefix, htprefix]
  · cases hsp

theorem spliceBytes_extract'_right {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64) (hi : off + value.size ≤ i) :
    out.extract' i j = template.extract' i j := by
  unfold ByteArray.extract'
  have hguard : (decide (i < 2 ^ 64) && decide (j < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact spliceBytes_extract_right hsp hi

theorem spliceBytes_get?_disjoint {template value out : ByteArray} {off i : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hdisj : PatchWindowDisjoint i (i + 1) (off, value)) :
    out.get? i = template.get? i := by
  rcases hdisj with hright | hleft
  · exact spliceBytes_get?_right hsp hright
  · exact spliceBytes_get?_left hsp (by omega)

theorem spliceBytes_extract_disjoint {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hdisj : PatchWindowDisjoint i j (off, value)) :
    out.extract i j = template.extract i j := by
  rcases hdisj with hright | hleft
  · exact spliceBytes_extract_right hsp hright
  · exact spliceBytes_extract_left hsp hleft

theorem spliceBytes_extract'_disjoint {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64)
    (hdisj : PatchWindowDisjoint i j (off, value)) :
    out.extract' i j = template.extract' i j := by
  rcases hdisj with hright | hleft
  · exact spliceBytes_extract'_right hsp hi64 hj64 hright
  · exact spliceBytes_extract'_left hsp hi64 hj64 hleft

theorem patchRuntime_get?_disjoint {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {i : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesWindowDisjoint32 i (i + 1) ps) :
    out.get? i = template.get? i := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp32 : PatchWindowDisjoint32 i (i + 1) p := hps p (by simp)
      have hrest : PatchesWindowDisjoint32 i (i + 1) ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            have hp : PatchWindowDisjoint i (i + 1) p := by
              rcases hp32 with hright | hleft
              · exact Or.inl (by simpa [hsz] using hright)
              · exact Or.inr hleft
            calc
              out.get? i = mid.get? i := ih hpatch hrest
              _ = template.get? i := spliceBytes_get?_disjoint hsp hp
      · rw [if_neg hsz] at hpatch
        simp at hpatch

theorem patchRuntime_D_J_aux_contains_of_patchScanReaches
    {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {fuel i target : Nat} (acc : Array UInt256)
    (hpatch : patchRuntime template ps = some out)
    (hscan : patchScanReaches fuel template (ps.map Prod.fst) i target = true) :
    (D_J_aux out i acc).contains (UInt256.ofNat target) = true := by
  induction fuel generalizing i acc with
  | zero =>
      simp [patchScanReaches] at hscan
  | succ fuel ih =>
      unfold patchScanReaches at hscan
      cases hdecode : template.get? i >>= parseInstr with
      | none =>
          simp [hdecode] at hscan
      | some op =>
          simp [hdecode] at hscan
          cases hdisjBool :
              patchOffsetsWindowDisjoint32Bool i (i + 1) (ps.map Prod.fst) with
          | false =>
              simp [hdisjBool] at hscan
          | true =>
              simp [hdisjBool] at hscan
              have hdisj : PatchesWindowDisjoint32 i (i + 1) ps :=
                patchesWindowDisjoint32_of_offsets_bool hdisjBool
              have hout : out.get? i >>= parseInstr = some op := by
                rw [patchRuntime_get?_disjoint hpatch hdisj]
                exact hdecode
              rw [D_J_aux_eq_some out i acc op hout]
              by_cases hhit : i = target ∧ op = .JUMPDEST
              · rw [D_J_aux_acc]
                simp [hhit.1, hhit.2]
              · have hnext :
                    patchScanReaches fuel template (ps.map Prod.fst) (N i op) target = true := by
                  simpa [hhit] using hscan
                exact ih (i := N i op)
                  (acc := if op = .JUMPDEST then acc.push (UInt256.ofNat i) else acc) hnext

theorem patchRuntime_D_J_contains_of_patchScanReaches
    {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {fuel target : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hscan : patchScanReaches fuel template (ps.map Prod.fst) 0 target = true) :
    (D_J out 0).contains (UInt256.ofNat target) = true := by
  simpa [D_J] using
    patchRuntime_D_J_aux_contains_of_patchScanReaches (acc := #[]) hpatch hscan

theorem patchRuntime_extract_disjoint {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {i j : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hps : PatchesWindowDisjoint32 i j ps) :
    out.extract i j = template.extract i j := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp32 : PatchWindowDisjoint32 i j p := hps p (by simp)
      have hrest : PatchesWindowDisjoint32 i j ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            have hp : PatchWindowDisjoint i j p := by
              rcases hp32 with hright | hleft
              · exact Or.inl (by simpa [hsz] using hright)
              · exact Or.inr hleft
            calc
              out.extract i j = mid.extract i j := ih hpatch hrest
              _ = template.extract i j := spliceBytes_extract_disjoint hsp hp
      · rw [if_neg hsz] at hpatch
        simp at hpatch

theorem patchRuntime_extract_exact_cons {template out value : ByteArray}
    {ps : List (Nat × ByteArray)} {off : Nat}
    (hpatch : patchRuntime template ((off, value) :: ps) = some out)
    (hsize : value.size = 32)
    (hps : PatchesWindowDisjoint32 off (off + 32) ps) :
    out.extract off (off + 32) = value := by
  unfold patchRuntime at hpatch
  simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
  rw [if_pos hsize] at hpatch
  cases hsp : spliceBytes? template off value with
  | none =>
      simp [hsp] at hpatch
  | some mid =>
      simp [hsp] at hpatch
      calc
        out.extract off (off + 32) = mid.extract off (off + 32) :=
          patchRuntime_extract_disjoint hpatch hps
        _ = value := by
          rw [← hsize]
          exact spliceBytes_extract_middle hsp

theorem patchRuntime_extract_exact_split {template out value : ByteArray}
    {pre post : List (Nat × ByteArray)} {off : Nat}
    (hpatch : patchRuntime template (pre ++ (off, value) :: post) = some out)
    (hsize : value.size = 32)
    (hpost : PatchesWindowDisjoint32 off (off + 32) post) :
    out.extract off (off + 32) = value := by
  induction pre generalizing template with
  | nil =>
      simpa using patchRuntime_extract_exact_cons hpatch hsize hpost
  | cons p pre ih =>
      change patchRuntime template (p :: (pre ++ (off, value) :: post)) = some out at hpatch
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hpsz : p.2.size = 32
      · rw [if_pos hpsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none =>
            simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            change ((List.foldlM
              (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none)
              mid pre).bind fun init =>
                List.foldlM
                  (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none)
                  init ((off, value) :: post)) = some out at hpatch
            have hpatch' : patchRuntime mid (pre ++ (off, value) :: post) = some out := by
              unfold patchRuntime
              rw [List.foldlM_append]
              exact hpatch
            exact ih hpatch'
      · rw [if_neg hpsz] at hpatch
        simp at hpatch

theorem patchRuntime_extract'_exact_split {template out value : ByteArray}
    {pre post : List (Nat × ByteArray)} {off : Nat}
    (hpatch : patchRuntime template (pre ++ (off, value) :: post) = some out)
    (hsize : value.size = 32)
    (hpost : PatchesWindowDisjoint32 off (off + 32) post)
    (hi64 : off < 2 ^ 64) (hj64 : off + 32 < 2 ^ 64) :
    out.extract' off (off + 32) = value := by
  unfold ByteArray.extract'
  have hguard : (decide (off < 2 ^ 64) && decide (off + 32 < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard]
  exact patchRuntime_extract_exact_split hpatch hsize hpost

theorem patchRuntime_extract'_disjoint {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {i j : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hps : PatchesWindowDisjoint32 i j ps) (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64) :
    out.extract' i j = template.extract' i j := by
  unfold ByteArray.extract'
  have hguard : (decide (i < 2 ^ 64) && decide (j < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact patchRuntime_extract_disjoint hpatch hps

theorem patchRuntime_decode_disjoint_of_decode {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {pc : UInt256}
    {res : Operation × Option (UInt256 × Nat)}
    (hpatch : patchRuntime template ps = some out)
    (hbyte : PatchesWindowDisjoint32 pc.toNat (pc.toNat + 1) ps)
    (hargs : ∀ byte instr, template.get? pc.toNat = some byte →
      parseInstr byte = some instr →
      PatchesWindowDisjoint32 (pc.toNat + 1)
        (pc.toNat + 1 + argOnNBytesOfInstr instr) ps)
    (hdec : decode template pc = some res)
    (hi64 : pc.toNat + 1 < 2 ^ 64)
    (harg64 : ∀ byte instr, template.get? pc.toNat = some byte →
      parseInstr byte = some instr → pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64) :
    decode out pc = some res := by
  unfold decode at hdec ⊢
  rw [patchRuntime_get?_disjoint hpatch hbyte]
  cases hget : template.get? pc.toNat with
  | none => simp [hget] at hdec
  | some byte =>
      simp [hget] at hdec
      cases hinstr : parseInstr byte with
      | none => simp [hinstr] at hdec
      | some instr =>
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [hinstr, harg] at hdec ⊢
            exact hdec
          · simp [hinstr, harg] at hdec
            cases hdec
            have hps := hargs byte instr hget hinstr
            have hj64 := harg64 byte instr hget hinstr
            simp [hinstr, harg]
            rw [patchRuntime_extract'_disjoint hpatch hps hi64 hj64]

theorem patchRuntime_decode_disjoint_of_decode_res {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {pc : UInt256}
    {res : Operation × Option (UInt256 × Nat)}
    (hpatch : patchRuntime template ps = some out)
    (hbyte : PatchesWindowDisjoint32 pc.toNat (pc.toNat + 1) ps)
    (hargs : PatchesWindowDisjoint32 (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) ps)
    (hdec : decode template pc = some res)
    (hi64 : pc.toNat + 1 < 2 ^ 64)
    (harg64 :
      pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) < 2 ^ 64) :
    decode out pc = some res := by
  unfold decode at hdec ⊢
  rw [patchRuntime_get?_disjoint hpatch hbyte]
  cases hget : template.get? pc.toNat with
  | none => simp [hget] at hdec
  | some byte =>
      simp [hget] at hdec
      cases hinstr : parseInstr byte with
      | none => simp [hinstr] at hdec
      | some instr =>
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [hinstr, harg] at hdec ⊢
            exact hdec
          · simp [hinstr, harg] at hdec
            cases hdec
            simp [hinstr, harg]
            rw [patchRuntime_extract'_disjoint hpatch hargs hi64 (by simpa using harg64)]

theorem spliceBytes_size_eq {template value out : ByteArray} {off : Nat}
    (hsp : spliceBytes? template off value = some out) :
    out.size = template.size := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  · cases hsp

theorem patchRuntime_size_eq {template out : ByteArray} {ps : List (Nat × ByteArray)}
    (hpatch : patchRuntime template ps = some out) :
    out.size = template.size := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none =>
            simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            rw [ih hpatch, spliceBytes_size_eq hsp]
      · rw [if_neg hsz] at hpatch
        simp at hpatch



theorem byteArray_prefix_suffix (b : ByteArray) (n : Nat) (hn : n ≤ b.size) :
    b.extract 0 n ++ b.extract n b.size = b := by
  rw [ByteArray.extract_append_extract]
  rw [show min 0 n = 0 by omega, show max n b.size = b.size by omega]
  exact byteArray_extract_self b

theorem spliceBytes?_eq_pref_append {pref rest value out : ByteArray} {offset : Nat}
    (h : spliceBytes? (pref ++ rest) offset value = some out) (hoff : pref.size ≤ offset) :
    ∃ rest', out = pref ++ rest' := by
  unfold spliceBytes? at h
  split at h
  · cases h
    refine ⟨rest.extract 0 (offset - pref.size) ++ value ++
      (pref ++ rest).extract (offset + value.size) (pref ++ rest).size, ?_⟩
    rw [Reasoning.Theory.extract_append_span]
    · rw [Reasoning.Theory.byteArray_extract_self]
      simp only [ByteArray.append_assoc]
    · omega
    · omega
  · simp at h

theorem patchRuntime_eq_pref_append_aux (ps : List (Nat × ByteArray))
    {pref acc out : ByteArray} (hacc : ∃ rest, acc = pref ++ rest)
    (hall : ∀ p ∈ ps, pref.size ≤ p.1)
    (h : ps.foldlM (fun acc p =>
      if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none) acc = some out) :
    ∃ rest, out = pref ++ rest := by
  induction ps generalizing acc with
  | nil =>
      simp at h
      cases h
      exact hacc
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at h
        rcases hacc with ⟨rest, rfl⟩
        cases hsp : spliceBytes? (pref ++ rest) p.1 p.2 with
        | none => simp [hsp] at h
        | some acc' =>
            simp [hsp] at h
            exact ih (hacc := spliceBytes?_eq_pref_append hsp (hall p (by simp)))
              (hall := fun q hq => hall q (by simp [hq])) h
      · rw [if_neg hsz] at h
        simp at h

theorem patchRuntime_eq_pref_append {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {n : Nat} (hn : n ≤ template.size)
    (hall : ∀ p ∈ ps, n ≤ p.1) (h : patchRuntime template ps = some out) :
    ∃ rest, out = template.extract 0 n ++ rest := by
  unfold patchRuntime at h
  refine patchRuntime_eq_pref_append_aux ps ?_ ?_ h
  · exact ⟨template.extract n template.size, (byteArray_prefix_suffix template n hn).symm⟩
  · intro p hp
    simpa [ByteArray.size_extract, hn] using hall p hp

def prefixWindowLt64 (bytes : ByteArray) (pc : UInt256) : Bool :=
  match bytes.get? pc.toNat with
  | some b =>
      match parseInstr b with
      | some instr => decide (pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64)
      | none => true
  | none => true

theorem prefixWindowLt64_of_true {bytes : ByteArray} {pc : UInt256}
    (hok : prefixWindowLt64 bytes pc = true) :
    ∀ b instr, bytes.get? pc.toNat = some b → parseInstr b = some instr →
      pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by
  intro b instr hb hparse
  unfold prefixWindowLt64 at hok
  simp only [hb, hparse] at hok
  exact of_decide_eq_true hok

theorem spliceBytes?_extract_before {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hbefore : stop ≤ offset) :
    out.extract start stop = b.extract start stop := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [ByteArray.append_assoc]
    rw [extract_append_left (b.extract 0 offset) (val ++ b.extract (offset + val.size) b.size)
      start stop]
    · rw [extract_extract_BA]
      rw [show min (0 + stop) offset = stop by omega]
      simp
    · rw [ByteArray.size_extract]
      omega
  · simp at h

theorem spliceBytes?_extract_after {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hafter : offset + val.size ≤ start) (hle : start ≤ stop) (hstop : stop ≤ b.size) :
    out.extract start stop = b.extract start stop := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [extract_append_right_window (b.extract 0 offset ++ val)
      (b.extract (offset + val.size) b.size) start stop]
    · rw [ByteArray.size_append, ByteArray.size_extract]
      rw [show min offset b.size = offset by omega]
      simp only [Nat.sub_zero]
      rw [extract_extract_BA]
      rw [show offset + val.size + (start - (offset + val.size)) = start by omega]
      rw [show min (offset + val.size + (stop - (offset + val.size))) b.size = stop by omega]
    · rw [ByteArray.size_append, ByteArray.size_extract]
      rw [show min offset b.size = offset by omega]
      omega
  · simp at h

theorem spliceBytes?_extract_disjoint {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hdisj : stop ≤ offset ∨ offset + val.size ≤ start) (hle : start ≤ stop)
    (hstop : stop ≤ b.size) :
    out.extract start stop = b.extract start stop := by
  rcases hdisj with hbefore | hafter
  · exact spliceBytes?_extract_before h hbefore
  · exact spliceBytes?_extract_after h hafter hle hstop

theorem spliceBytes?_size_eq {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    out.size = b.size := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  · simp at h

theorem spliceBytes?_extract_patch {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    out.extract offset (offset + val.size) = val := by
  unfold spliceBytes? at h
  split at h
  · cases h
    rw [ByteArray.append_assoc]
    rw [extract_append_right_window (b.extract 0 offset)
      (val ++ b.extract (offset + val.size) b.size) offset (offset + val.size)]
    · rw [ByteArray.size_extract]
      have hoff : offset ≤ b.size := by omega
      rw [show min offset b.size = offset by omega]
      rw [show offset - (offset - 0) = 0 by omega]
      rw [show offset + val.size - (offset - 0) = val.size by omega]
      rw [extract_append_left val (b.extract (offset + val.size) b.size) 0 val.size]
      · exact byteArray_extract_self val
      · omega
    · rw [ByteArray.size_extract]
      omega
  · simp at h

theorem spliceBytes?_offset_add_size_le {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    offset + val.size ≤ b.size := by
  unfold spliceBytes? at h
  split at h
  · assumption
  · simp at h

theorem patchRuntime_extract_eq_aux (ps : List (Nat × ByteArray))
    {template acc out : ByteArray} {start stop : Nat}
    (hextract : acc.extract start stop = template.extract start stop)
    (hsize : acc.size = template.size)
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : ps.foldlM (fun acc p =>
      if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none) acc = some out) :
    out.extract start stop = template.extract start stop ∧ out.size = template.size := by
  induction ps generalizing acc with
  | nil =>
      simp at h
      cases h
      exact ⟨hextract, hsize⟩
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      by_cases hszp : p.2.size = 32
      · rw [if_pos hszp] at h
        cases hsp : spliceBytes? acc p.1 p.2 with
        | none => simp [hsp] at h
        | some acc' =>
            simp [hsp] at h
            have hdisj' : stop ≤ p.1 ∨ p.1 + p.2.size ≤ start := by
              simpa [hszp] using hdisj p (by simp)
            have hacc' : acc'.extract start stop = template.extract start stop := by
              rw [spliceBytes?_extract_disjoint hsp hdisj' hle (by rw [hsize]; exact hstop)]
              exact hextract
            have hsize' : acc'.size = template.size := by
              rw [spliceBytes?_size_eq hsp, hsize]
            exact ih hacc' hsize'
              (fun q hq => hdisj q (List.mem_cons_of_mem p hq)) h
      · rw [if_neg hszp] at h
        simp at h

theorem patchRuntime_extract_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {start stop : Nat}
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : patchRuntime template ps = some out) :
    out.extract start stop = template.extract start stop := by
  unfold patchRuntime at h
  exact (patchRuntime_extract_eq_aux ps (template := template) (acc := template)
    (out := out) (start := start) (stop := stop) rfl rfl hle hstop hdisj h).1

theorem patchRuntime_extract_patch {template out value : ByteArray}
    {pre post : List (Nat × ByteArray)} {offset : Nat}
    (hvalue : value.size = 32)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (h : patchRuntime template (pre ++ (offset, value) :: post) = some out) :
    out.extract offset (offset + 32) = value := by
  unfold patchRuntime at h
  rw [List.foldlM_append] at h
  cases hpre : List.foldlM
      (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none)
      template pre with
  | none => simp [hpre] at h
  | some accPre =>
      simp [hpre, hvalue] at h
      cases hsp : spliceBytes? accPre offset value with
      | none => simp [hsp] at h
      | some accTarget =>
          simp [hsp] at h
          have htarget : accTarget.extract offset (offset + 32) = value := by
            simpa [hvalue] using spliceBytes?_extract_patch hsp
          have htargetSize : offset + 32 ≤ accTarget.size := by
            rw [spliceBytes?_size_eq hsp]
            simpa [hvalue] using spliceBytes?_offset_add_size_le hsp
          have htail := patchRuntime_extract_eq_aux post (template := accTarget)
            (acc := accTarget) (out := out) (start := offset) (stop := offset + 32)
            rfl rfl (by omega) htargetSize hpost h
          exact htail.1.trans htarget

theorem patchRuntime_extract'_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {start stop : Nat}
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hstart64 : start < 2 ^ 64) (hstop64 : stop < 2 ^ 64)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : patchRuntime template ps = some out) :
    out.extract' start stop = template.extract' start stop := by
  unfold ByteArray.extract'
  have hguard : (decide (start < 2 ^ 64) && decide (stop < 2 ^ 64)) = true := by
    rw [decide_eq_true hstart64, decide_eq_true hstop64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact patchRuntime_extract_eq hle hstop hdisj h

theorem get?_eq_of_extract_one {a b : ByteArray} {idx : Nat}
    (ha : idx < a.size) (hb : idx < b.size)
    (h : a.extract idx (idx + 1) = b.extract idx (idx + 1)) :
    a.get? idx = b.get? idx := by
  unfold ByteArray.get?
  simp only [dif_pos ha, dif_pos hb]
  have hdata := congrArg ByteArray.data h
  have hlist := congrArg Array.toList hdata
  rw [ByteArray.data_extract, ByteArray.data_extract, Array.toList_extract,
    Array.toList_extract, List.extract_eq_take_drop, List.extract_eq_take_drop] at hlist
  have hleft : (List.take (idx + 1 - idx) (List.drop idx a.data.toList))[0]? =
      some (a.get idx ha) := by
    simp [ByteArray.get]
  have hright : (List.take (idx + 1 - idx) (List.drop idx b.data.toList))[0]? =
      some (b.get idx hb) := by
    simp [ByteArray.get]
  have hget := congrArg (fun xs : List UInt8 => xs[0]?) hlist
  change (List.take (idx + 1 - idx) (List.drop idx a.data.toList))[0]? =
      (List.take (idx + 1 - idx) (List.drop idx b.data.toList))[0]? at hget
  rw [hleft, hright] at hget
  exact hget

theorem lt_size_of_get?_bind_parseInstr_some {c : ByteArray} {i : ℕ}
    {instr : Operation} (h : c.get? i >>= parseInstr = some instr) : i < c.size := by
  rcases hb : c.get? i with _ | b
  · rw [hb] at h
    simp at h
  · rw [ByteArray.get?] at hb
    split at hb
    · assumption
    · simp at hb

set_option linter.unusedVariables false in
def D_J_auxPreservesTargetBool (template : ByteArray) (offsets : List Nat)
    (target : UInt256) (i : Nat) : Bool :=
  offsets.all (fun offset => decide (i + 1 ≤ offset ∨ offset + 32 ≤ i)) &&
    match hget : template.get? i >>= parseInstr with
    | none => false
    | some instr =>
        if instr = .JUMPDEST ∧ UInt256.ofNat i = target then
          true
        else
          D_J_auxPreservesTargetBool template offsets target (N i instr)
termination_by template.size - i
decreasing_by
  have hN : i < N i instr := by
    simp [N]
    omega
  have hi : i < template.size :=
    lt_size_of_get?_bind_parseInstr_some hget
  omega

theorem patchRuntime_parse_eq_of_disjoint {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {i : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hdisj : ∀ p ∈ ps, i + 1 ≤ p.1 ∨ p.1 + 32 ≤ i) :
    out.get? i >>= parseInstr = template.get? i >>= parseInstr := by
  by_cases hi : i < template.size
  · have hsize := patchRuntime_size_eq hpatch
    have hget : out.get? i = template.get? i := by
      apply get?_eq_of_extract_one (by rw [hsize]; exact hi) hi
      exact patchRuntime_extract_eq (by omega) (by omega) hdisj hpatch
    rw [hget]
  · have hsize := patchRuntime_size_eq hpatch
    have hout : out.get? i = none := by
      rw [ByteArray.get?, dif_neg]
      rw [hsize]
      omega
    have htemplate : template.get? i = none := by
      rw [ByteArray.get?, dif_neg]
      omega
    rw [hout, htemplate]

theorem D_J_aux_contains_push_target {code : ByteArray} {i : Nat}
    {result : Array UInt256} :
    (D_J_aux code (N i .JUMPDEST) (result.push (UInt256.ofNat i))).contains
      (UInt256.ofNat i) = true := by
  rw [D_J_aux_acc]
  rw [Array.contains_iff_mem]
  simp

theorem D_J_aux_contains_of_patchRuntime_preservesTarget {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {offsets : List Nat} {target : UInt256} {i : Nat}
    {result : Array UInt256}
    (hpatch : patchRuntime template ps = some out)
    (hoffsets : ∀ p ∈ ps, p.1 ∈ offsets)
    (hscan : D_J_auxPreservesTargetBool template offsets target i = true) :
    (D_J_aux out i result).contains target = true := by
  rw [D_J_auxPreservesTargetBool] at hscan
  cases htemplate : template.get? i >>= parseInstr with
  | none =>
      rw [htemplate] at hscan
      simp at hscan
  | some instr =>
      rw [htemplate] at hscan
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hscan
      rcases hscan with ⟨hdisj, htail⟩
      have hpatchDisj : ∀ p ∈ ps, i + 1 ≤ p.1 ∨ p.1 + 32 ≤ i := by
        intro p hp
        exact hdisj p.1 (hoffsets p hp)
      have hparse := patchRuntime_parse_eq_of_disjoint hpatch hpatchDisj
      rw [D_J_aux_eq_some out i result instr (by rw [hparse, htemplate])]
      by_cases htarget : instr = .JUMPDEST ∧ UInt256.ofNat i = target
      · rw [if_pos htarget] at htail
        rcases htarget with ⟨rfl, htarget⟩
        rw [← htarget]
        exact D_J_aux_contains_push_target
      · rw [if_neg htarget] at htail
        exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch hoffsets htail
termination_by template.size - i
decreasing_by
  have hi := lt_size_of_get?_bind_parseInstr_some htemplate
  simp [N]
  omega

end Reasoning.Theory
