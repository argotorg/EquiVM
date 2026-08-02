import Examples.Ripemd160.HashFinal

/-!
# RIPEMD-160 pure compression bridge

This module relates the optimized runtime's `UInt256` compression expressions to the natural-
number RIPEMD-160 model. Runtime values are projected to 32-bit bitvectors so modular arithmetic,
Boolean functions, rotations, and the fixed lookup tables can be proved independently of memory.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Ripemd160

def lo32 (x : UInt256) : BitVec 32 := BitVec.ofNat 32 x.toNat

theorem lo32_land (a b : UInt256) : lo32 (UInt256.land a b) = lo32 a &&& lo32 b := by
  apply BitVec.eq_of_toNat_eq
  simp [lo32, uland_toNat]

theorem lo32_lor (a b : UInt256) : lo32 (UInt256.lor a b) = lo32 a ||| lo32 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.toNat_ofNat, BitVec.toNat_or, u256_lor_toNat]
  rw [show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_mod_of_dvd _ (by exact pow_dvd_pow 2 (by omega : 32 ≤ 256))]
  exact Nat.or_mod_two_pow

theorem uxor_toNat (a b : UInt256) :
    (UInt256.xor a b).toNat = (a.toNat ^^^ b.toNat) % UInt256.size := rfl

theorem lo32_xor (a b : UInt256) : lo32 (UInt256.xor a b) = lo32 a ^^^ lo32 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.toNat_ofNat, BitVec.toNat_xor, uxor_toNat]
  rw [show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_mod_of_dvd _ (by exact pow_dvd_pow 2 (by omega : 32 ≤ 256)),
    Nat.xor_mod_two_pow]

theorem lnot_toNat_small (x : UInt256) (_hx : x.toNat < 2 ^ 32) :
    (UInt256.lnot x).toNat = UInt256.size - 1 - x.toNat := by
  unfold UInt256.lnot
  change (UInt256.sub (UInt256.ofNat (UInt256.size - 1)) x).toNat = _
  have htop : UInt256.size - 1 < UInt256.size := by
    rw [UInt256.size]
    omega
  rw [usub_toNat]
  · rw [ulit_toNat' _ htop]
  · rw [ulit_toNat' _ htop]
    exact Nat.le_pred_of_lt x.val.isLt

theorem lo32_lnot (x : UInt256) (hx : x.toNat < 2 ^ 32) :
    lo32 (UInt256.lnot x) = ~~~lo32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not]
  simp only [lo32, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hx, lnot_toNat_small x hx]
  rw [show UInt256.size = 2 ^ 256 from by decide]
  have hdecomp :
      2 ^ 256 - 1 - x.toNat = (2 ^ 224 - 1) * 2 ^ 32 + (2 ^ 32 - 1 - x.toNat) := by
    omega
  rw [hdecomp]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
    Nat.zero_mod, Nat.zero_add,
    Nat.mod_eq_of_lt (by omega : 2 ^ 32 - 1 - x.toNat < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

theorem lo32_add (a b : UInt256) : lo32 (a + b) = lo32 a + lo32 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.toNat_ofNat, BitVec.toNat_add, uadd_toNat]
  rw [show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_mod_of_dvd _ (by exact pow_dvd_pow 2 (by omega : 32 ≤ 256)),
    Nat.add_mod]

theorem lo32_shl (x : UInt256) (n : Nat) (hx : x.toNat < 2 ^ 32)
    (hn : n < 256) :
    lo32 (UInt256.shiftLeft x (UInt256.ofNat n)) = lo32 x <<< n := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  rw [ushl_ofNat_toNat x n hn, show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_mod_of_dvd _ (by exact pow_dvd_pow 2 (by omega : 32 ≤ 256)),
    Nat.mod_eq_of_lt hx]

theorem lo32_shr (x : UInt256) (n : Nat) (hx : x.toNat < 2 ^ 32)
    (hn : n < 256) :
    lo32 (UInt256.shiftRight x (UInt256.ofNat n)) = lo32 x >>> n := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  rw [ushr_ofNat_toNat x n hn, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)]

theorem runtimeMask32_toNat (x : UInt256) :
    (UInt256.land mask32Word x).toNat = x.toNat % 2 ^ 32 := by
  unfold mask32Word
  rw [uland_toNat, show (⟨0xffffffff⟩ : UInt256).toNat = 2 ^ 32 - 1 by decide,
    Nat.and_comm]
  exact nat_land_mask_eq_mod _ _

theorem runtimeMask32_lt (x : UInt256) :
    (UInt256.land mask32Word x).toNat < 2 ^ 32 := by
  rw [runtimeMask32_toNat]
  exact Nat.mod_lt _ (by positivity)

theorem lo32_runtimeMask32 (x : UInt256) :
    lo32 (UInt256.land mask32Word x) = lo32 x := by
  apply BitVec.eq_of_toNat_eq
  simp [lo32, runtimeMask32_toNat]

theorem modelLeftF_lt (group b c d : Nat) : Model.leftF group b c d < 2 ^ 32 := by
  unfold Model.leftF
  split <;> exact lt_of_le_of_lt Nat.and_le_right (by norm_num [Model.mask32, Model.modulus32])

theorem modelRightF_lt (group b c d : Nat) : Model.rightF group b c d < 2 ^ 32 := by
  unfold Model.rightF
  split <;> exact lt_of_le_of_lt Nat.and_le_right (by norm_num [Model.mask32, Model.modulus32])

theorem lo32_runtimeLeftF {group : Nat} (hg : group < 5)
    {b c d : UInt256} (hb : b.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32)
    (hd : d.toNat < 2 ^ 32) :
    lo32 (runtimeLeftF group b c d) =
      BitVec.ofNat 32 (Model.leftF group b.toNat c.toNat d.toNat) := by
  interval_cases group <;>
    simp_all [runtimeLeftF, Model.leftF, Model.not32, Model.mask32, Model.modulus32,
      lo32_land, lo32_lor, lo32_xor, lo32_lnot] <;>
    simp only [lo32] <;> bv_decide

theorem lo32_runtimeRightF {group : Nat} (hg : group < 5)
    {b c d : UInt256} (hb : b.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32)
    (hd : d.toNat < 2 ^ 32) :
    lo32 (runtimeRightF group b c d) =
      BitVec.ofNat 32 (Model.rightF group b.toNat c.toNat d.toNat) := by
  interval_cases group <;>
    simp_all [runtimeRightF, Model.rightF, Model.not32, Model.mask32, Model.modulus32,
      lo32_land, lo32_lor, lo32_xor, lo32_lnot] <;>
    simp only [lo32] <;> bv_decide

theorem runtimeLeftWordEntry (group round : Nat) (hg : group < 5)
    (hr : round < 16) :
    runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round) =
      UInt256.ofNat (Model.rowEntry (Model.leftWordRow group) round) := by
  interval_cases group <;> interval_cases round <;> native_decide

theorem runtimeLeftRotationEntry (group round : Nat) (hg : group < 5)
    (hr : round < 16) :
    runtimeRowEntry (leftRotationRowWord group) (UInt256.ofNat round) =
      UInt256.ofNat (Model.rowEntry (Model.leftRotationRow group) round) := by
  interval_cases group <;> interval_cases round <;> native_decide

theorem runtimeRightWordEntry (group round : Nat) (hg : group < 5)
    (hr : round < 16) :
    runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round) =
      UInt256.ofNat (Model.rowEntry (Model.rightWordRow group) round) := by
  interval_cases group <;> interval_cases round <;> native_decide

theorem runtimeRightRotationEntry (group round : Nat) (hg : group < 5)
    (hr : round < 16) :
    runtimeRowEntry (rightRotationRowWord group) (UInt256.ofNat round) =
      UInt256.ofNat (Model.rowEntry (Model.rightRotationRow group) round) := by
  interval_cases group <;> interval_cases round <;> native_decide

theorem leftConstantWord_toNat (group : Nat) (hg : group < 5) :
    (leftConstantWord group).toNat = Model.leftConstant group := by
  interval_cases group <;> native_decide

theorem rightConstantWord_toNat (group : Nat) (hg : group < 5) :
    (rightConstantWord group).toNat = Model.rightConstant group := by
  interval_cases group <;> native_decide

theorem modelRol32_lt (x s : Nat) : Model.rol32 x s < 2 ^ 32 := by
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num [Model.mask32, Model.modulus32])

theorem u256_sub_32_ofNat (s : Nat) (hs : s ≤ 32) :
    (⟨32⟩ : UInt256) - UInt256.ofNat s = UInt256.ofNat (32 - s) := by
  change UInt256.sub (UInt256.ofNat 32) (UInt256.ofNat s) = _
  apply u256_inj
  rw [usub_toNat (by
      change s % UInt256.size ≤ 32 % UInt256.size
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hs (by decide)),
        Nat.mod_eq_of_lt (by decide)]
      exact hs),
    ulit_toNat' 32 (by decide),
    ulit_toNat' s (lt_of_le_of_lt hs (by decide)),
    ulit_toNat' (32 - s) (lt_of_le_of_lt (Nat.sub_le 32 s) (by decide))]

theorem bv32_ofNat_shl (x n : Nat) (hx : x < 2 ^ 32) :
    BitVec.ofNat 32 (x <<< n) = BitVec.ofNat 32 x <<< n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  rw [Nat.mod_eq_of_lt hx]

theorem bv32_ofNat_shr (x n : Nat) (hx : x < 2 ^ 32) :
    BitVec.ofNat 32 (x >>> n) = BitVec.ofNat 32 x >>> n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  rw [Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)]

theorem runtimeRol32_toNat (value : UInt256) (shift : Nat)
    (hv : value.toNat < 2 ^ 32) (hs : shift < 16) :
    (runtimeRol32 value (UInt256.ofNat shift)).toNat =
      Model.rol32 value.toNat shift := by
  have hproj : lo32 (runtimeRol32 value (UInt256.ofNat shift)) =
      BitVec.ofNat 32 (Model.rol32 value.toNat shift) := by
    unfold runtimeRol32 Model.rol32
    rw [lo32_runtimeMask32, lo32_lor, lo32_shl value shift hv (by omega),
      u256_sub_32_ofNat shift (by omega), lo32_shr value (32 - shift) hv (by omega)]
    interval_cases shift <;>
      simp [lo32, Model.mask32, Model.modulus32,
        bv32_ofNat_shl _ _ hv, bv32_ofNat_shr _ _ hv] <;> bv_decide
  have hout : (runtimeRol32 value (UInt256.ofNat shift)).toNat < 2 ^ 32 := by
    unfold runtimeRol32
    exact runtimeMask32_lt _
  have hmodel := modelRol32_lt value.toNat shift
  have hnat := congrArg BitVec.toNat hproj
  simp only [lo32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hout,
    Nat.mod_eq_of_lt hmodel] at hnat
  exact hnat

theorem runtimeMask32_add_toNat (a b : UInt256) :
    (UInt256.land mask32Word (a + b)).toNat =
      Model.u32 (a.toNat + b.toNat) := by
  rw [runtimeMask32_toNat, uadd_toNat]
  unfold Model.u32 Model.modulus32
  rw [show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_mod_of_dvd _ (by exact pow_dvd_pow 2 (by omega : 32 ≤ 256))]

theorem runtimeMask32_add4_toNat (a b c d : UInt256) :
    (UInt256.land mask32Word (a + b + c + d)).toNat =
      Model.u32 (a.toNat + b.toNat + c.toNat + d.toNat) := by
  have hproj : lo32 (UInt256.land mask32Word (a + b + c + d)) =
      lo32 a + lo32 b + lo32 c + lo32 d := by
    rw [lo32_runtimeMask32, lo32_add, lo32_add, lo32_add]
  have hnat := congrArg BitVec.toNat hproj
  simp only [lo32, BitVec.toNat_ofNat, BitVec.toNat_add] at hnat
  rw [runtimeMask32_toNat] at hnat
  unfold Model.u32 Model.modulus32
  rw [runtimeMask32_toNat]
  simpa [Nat.add_mod] using hnat

theorem runtimeMask32_add3_toNat (a b c : UInt256) :
    (UInt256.land mask32Word (a + b + c)).toNat =
      Model.u32 (a.toNat + b.toNat + c.toNat) := by
  have hproj : lo32 (UInt256.land mask32Word (a + b + c)) =
      lo32 a + lo32 b + lo32 c := by
    rw [lo32_runtimeMask32, lo32_add, lo32_add]
  have hnat := congrArg BitVec.toNat hproj
  simp only [lo32, BitVec.toNat_ofNat, BitVec.toNat_add] at hnat
  rw [runtimeMask32_toNat] at hnat
  unfold Model.u32 Model.modulus32
  rw [runtimeMask32_toNat]
  simpa [Nat.add_mod] using hnat

def Model.LineBound (s : Model.LineState) : Prop :=
  s.a < 2 ^ 32 ∧ s.b < 2 ^ 32 ∧ s.c < 2 ^ 32 ∧ s.d < 2 ^ 32 ∧ s.e < 2 ^ 32

def RuntimeLineRep (runtime : RuntimeLineState) (model : Model.LineState) : Prop :=
  runtime.a.toNat = model.a ∧ runtime.b.toNat = model.b ∧
  runtime.c.toNat = model.c ∧ runtime.d.toNat = model.d ∧ runtime.e.toNat = model.e

theorem Model.lineBound_leftRound (data : ByteArray) (block group round : Nat)
    (s : Model.LineState) (hs : Model.LineBound s) :
    Model.LineBound (Model.leftRound data block group round s) := by
  rcases hs with ⟨ha, hb, hc, hd, he⟩
  unfold Model.leftRound Model.LineBound
  dsimp only
  exact ⟨he, Nat.mod_lt _ (by norm_num [Model.modulus32]), hb, modelRol32_lt _ _, hd⟩

theorem Model.lineBound_rightRound (data : ByteArray) (block group round : Nat)
    (s : Model.LineState) (hs : Model.LineBound s) :
    Model.LineBound (Model.rightRound data block group round s) := by
  rcases hs with ⟨ha, hb, hc, hd, he⟩
  unfold Model.rightRound Model.LineBound
  dsimp only
  exact ⟨he, Nat.mod_lt _ (by norm_num [Model.modulus32]), hb, modelRol32_lt _ _, hd⟩

theorem runtimePureLeftRound_rep (data : ByteArray) (block group round : Nat)
    (X : Fin 16 → UInt256) (runtime : RuntimeLineState) (model : Model.LineState)
    (hg : group < 5) (hr : round < 16)
    (hX : ∀ i, (X i).toNat = Model.blockWord data block i.val)
    (hrep : RuntimeLineRep runtime model) (hbound : Model.LineBound model) :
    RuntimeLineRep (runtimePureLeftRound X group round runtime)
      (Model.leftRound data block group round model) := by
  rcases hrep with ⟨ha, hb, hc, hd, he⟩
  rcases hbound with ⟨hma, hmb, hmc, hmd, hme⟩
  have hbnd : runtime.b.toNat < 2 ^ 32 := by omega
  have hcnd : runtime.c.toNat < 2 ^ 32 := by omega
  have hdnd : runtime.d.toNat < 2 ^ 32 := by omega
  have hfproj := lo32_runtimeLeftF hg hbnd hcnd hdnd
  have hf : (UInt256.land mask32Word
      (runtimeLeftF group runtime.b runtime.c runtime.d)).toNat =
      Model.leftF group model.b model.c model.d := by
    have h := congrArg BitVec.toNat hfproj
    simp only [lo32, BitVec.toNat_ofNat] at h
    rw [Nat.mod_eq_of_lt (modelLeftF_lt group runtime.b.toNat runtime.c.toNat runtime.d.toNat)] at h
    rw [runtimeMask32_toNat]
    simpa [hb, hc, hd] using h
  let ri := Model.rowEntry (Model.leftWordRow group) round
  let si := Model.rowEntry (Model.leftRotationRow group) round
  have hri : ri < 16 := by
    dsimp only [ri]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  have hsi : si < 16 := by
    dsimp only [si]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  have hword := runtimeLeftWordEntry group round hg hr
  have hrot := runtimeLeftRotationEntry group round hg hr
  let runtimeRi : Fin 16 :=
    ⟨(runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round)).toNat,
      runtimeRowEntry_lt_sixteen _ _⟩
  have hruntimeRi : runtimeRi = ⟨ri, hri⟩ := by
    apply Fin.ext
    dsimp only [runtimeRi, ri]
    rw [hword, ulit_toNat' _ (lt_trans hri (by decide))]
  have hx :
      (X ⟨(runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩).toNat = Model.blockWord data block ri := by
    change (X runtimeRi).toNat = _
    rw [hruntimeRi]
    exact hX ⟨ri, hri⟩
  have hk := leftConstantWord_toNat group hg
  let sumWord := UInt256.land mask32Word
    (UInt256.land mask32Word (runtimeLeftF group runtime.b runtime.c runtime.d) +
      runtime.a +
      X ⟨(runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩ + leftConstantWord group)
  have hsum : sumWord.toNat =
      Model.u32 (model.a + Model.leftF group model.b model.c model.d +
        Model.blockWord data block ri + Model.leftConstant group) := by
    dsimp only [sumWord]
    rw [runtimeMask32_add4_toNat, hf, ha, hx, hk]
    congr 1
    omega
  have hsumBound : sumWord.toNat < 2 ^ 32 := by
    dsimp only [sumWord]
    exact runtimeMask32_lt _
  have hrol :
      (runtimeRol32 sumWord (runtimeRowEntry (leftRotationRowWord group)
        (UInt256.ofNat round))).toNat =
      Model.rol32
        (Model.u32 (model.a + Model.leftF group model.b model.c model.d +
          Model.blockWord data block ri + Model.leftConstant group)) si := by
    rw [hrot]
    simpa [hsum] using runtimeRol32_toNat sumWord si hsumBound hsi
  unfold runtimePureLeftRound runtimePureRound runtimePureRoundNext Model.leftRound
  dsimp only
  refine ⟨he, ?_, hb, ?_, hd⟩
  · rw [runtimeMask32_add_toNat, hrol, he]
  · simpa [hc] using runtimeRol32_toNat runtime.c 10 (by omega) (by decide)

theorem runtimePureRightRound_rep (data : ByteArray) (block group round : Nat)
    (X : Fin 16 → UInt256) (runtime : RuntimeLineState) (model : Model.LineState)
    (hg : group < 5) (hr : round < 16)
    (hX : ∀ i, (X i).toNat = Model.blockWord data block i.val)
    (hrep : RuntimeLineRep runtime model) (hbound : Model.LineBound model) :
    RuntimeLineRep (runtimePureRightRound X group round runtime)
      (Model.rightRound data block group round model) := by
  rcases hrep with ⟨ha, hb, hc, hd, he⟩
  rcases hbound with ⟨hma, hmb, hmc, hmd, hme⟩
  have hbnd : runtime.b.toNat < 2 ^ 32 := by omega
  have hcnd : runtime.c.toNat < 2 ^ 32 := by omega
  have hdnd : runtime.d.toNat < 2 ^ 32 := by omega
  have hfproj := lo32_runtimeRightF hg hbnd hcnd hdnd
  have hf : (UInt256.land mask32Word
      (runtimeRightF group runtime.b runtime.c runtime.d)).toNat =
      Model.rightF group model.b model.c model.d := by
    have h := congrArg BitVec.toNat hfproj
    simp only [lo32, BitVec.toNat_ofNat] at h
    rw [Nat.mod_eq_of_lt (modelRightF_lt group runtime.b.toNat runtime.c.toNat runtime.d.toNat)] at h
    rw [runtimeMask32_toNat]
    simpa [hb, hc, hd] using h
  let ri := Model.rowEntry (Model.rightWordRow group) round
  let si := Model.rowEntry (Model.rightRotationRow group) round
  have hri : ri < 16 := by
    dsimp only [ri]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  have hsi : si < 16 := by
    dsimp only [si]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)
  have hword := runtimeRightWordEntry group round hg hr
  have hrot := runtimeRightRotationEntry group round hg hr
  let runtimeRi : Fin 16 :=
    ⟨(runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round)).toNat,
      runtimeRowEntry_lt_sixteen _ _⟩
  have hruntimeRi : runtimeRi = ⟨ri, hri⟩ := by
    apply Fin.ext
    dsimp only [runtimeRi, ri]
    rw [hword, ulit_toNat' _ (lt_trans hri (by decide))]
  have hx :
      (X ⟨(runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩).toNat = Model.blockWord data block ri := by
    change (X runtimeRi).toNat = _
    rw [hruntimeRi]
    exact hX ⟨ri, hri⟩
  have hk := rightConstantWord_toNat group hg
  let sumWord := UInt256.land mask32Word
    (UInt256.land mask32Word (runtimeRightF group runtime.b runtime.c runtime.d) +
      runtime.a +
      X ⟨(runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩ + rightConstantWord group)
  have hsum : sumWord.toNat =
      Model.u32 (model.a + Model.rightF group model.b model.c model.d +
        Model.blockWord data block ri + Model.rightConstant group) := by
    dsimp only [sumWord]
    rw [runtimeMask32_add4_toNat, hf, ha, hx, hk]
    congr 1
    omega
  have hsumBound : sumWord.toNat < 2 ^ 32 := by
    dsimp only [sumWord]
    exact runtimeMask32_lt _
  have hrol :
      (runtimeRol32 sumWord (runtimeRowEntry (rightRotationRowWord group)
        (UInt256.ofNat round))).toNat =
      Model.rol32
        (Model.u32 (model.a + Model.rightF group model.b model.c model.d +
          Model.blockWord data block ri + Model.rightConstant group)) si := by
    rw [hrot]
    simpa [hsum] using runtimeRol32_toNat sumWord si hsumBound hsi
  unfold runtimePureRightRound runtimePureRound runtimePureRoundNext Model.rightRound
  dsimp only
  refine ⟨he, ?_, hb, ?_, hd⟩
  · rw [runtimeMask32_add_toNat, hrol, he]
  · simpa [hc] using runtimeRol32_toNat runtime.c 10 (by omega) (by decide)

theorem runtimePureLeftGroup_rep (data : ByteArray) (block group rounds : Nat)
    (X : Fin 16 → UInt256) (runtime : RuntimeLineState) (model : Model.LineState)
    (hg : group < 5) (hrounds : rounds ≤ 16)
    (hX : ∀ i, (X i).toNat = Model.blockWord data block i.val)
    (hrep : RuntimeLineRep runtime model) (hbound : Model.LineBound model) :
    RuntimeLineRep (runtimePureLeftGroup X group rounds runtime)
      (Model.leftGroup data block group rounds model) ∧
    Model.LineBound (Model.leftGroup data block group rounds model) := by
  induction rounds with
  | zero => exact ⟨hrep, hbound⟩
  | succ round ih =>
      have hprev := ih (by omega)
      exact ⟨runtimePureLeftRound_rep data block group round X _ _ hg (by omega)
          hX hprev.1 hprev.2,
        Model.lineBound_leftRound data block group round _ hprev.2⟩

theorem runtimePureRightGroup_rep (data : ByteArray) (block group rounds : Nat)
    (X : Fin 16 → UInt256) (runtime : RuntimeLineState) (model : Model.LineState)
    (hg : group < 5) (hrounds : rounds ≤ 16)
    (hX : ∀ i, (X i).toNat = Model.blockWord data block i.val)
    (hrep : RuntimeLineRep runtime model) (hbound : Model.LineBound model) :
    RuntimeLineRep (runtimePureRightGroup X group rounds runtime)
      (Model.rightGroup data block group rounds model) ∧
    Model.LineBound (Model.rightGroup data block group rounds model) := by
  induction rounds with
  | zero => exact ⟨hrep, hbound⟩
  | succ round ih =>
      have hprev := ih (by omega)
      exact ⟨runtimePureRightRound_rep data block group round X _ _ hg (by omega)
          hX hprev.1 hprev.2,
        Model.lineBound_rightRound data block group round _ hprev.2⟩

theorem runtimePureLeftLine_rep (data : ByteArray) (block groups : Nat)
    (X : Fin 16 → UInt256) (runtime : RuntimeLineState) (model : Model.LineState)
    (hgroups : groups ≤ 5)
    (hX : ∀ i, (X i).toNat = Model.blockWord data block i.val)
    (hrep : RuntimeLineRep runtime model) (hbound : Model.LineBound model) :
    RuntimeLineRep (runtimePureLeftLine X groups runtime)
      (Model.leftLine data block groups model) ∧
    Model.LineBound (Model.leftLine data block groups model) := by
  induction groups with
  | zero => exact ⟨hrep, hbound⟩
  | succ group ih =>
      have hprev := ih (by omega)
      exact runtimePureLeftGroup_rep data block group 16 X _ _ (by omega) (by omega)
        hX hprev.1 hprev.2

theorem runtimePureRightLine_rep (data : ByteArray) (block groups : Nat)
    (X : Fin 16 → UInt256) (runtime : RuntimeLineState) (model : Model.LineState)
    (hgroups : groups ≤ 5)
    (hX : ∀ i, (X i).toNat = Model.blockWord data block i.val)
    (hrep : RuntimeLineRep runtime model) (hbound : Model.LineBound model) :
    RuntimeLineRep (runtimePureRightLine X groups runtime)
      (Model.rightLine data block groups model) ∧
    Model.LineBound (Model.rightLine data block groups model) := by
  induction groups with
  | zero => exact ⟨hrep, hbound⟩
  | succ group ih =>
      have hprev := ih (by omega)
      exact runtimePureRightGroup_rep data block group 16 X _ _ (by omega) (by omega)
        hX hprev.1 hprev.2

def Model.ChainBound (h : Model.ChainState) : Prop :=
  h.h0 < 2 ^ 32 ∧ h.h1 < 2 ^ 32 ∧ h.h2 < 2 ^ 32 ∧ h.h3 < 2 ^ 32 ∧ h.h4 < 2 ^ 32

def RuntimeChainRep (runtime : RuntimeChain) (model : Model.ChainState) : Prop :=
  runtime.h0.toNat = model.h0 ∧ runtime.h1.toNat = model.h1 ∧
  runtime.h2.toNat = model.h2 ∧ runtime.h3.toNat = model.h3 ∧ runtime.h4.toNat = model.h4

theorem runtimeLineOfChain_rep {runtime : RuntimeChain} {model : Model.ChainState}
    (hrep : RuntimeChainRep runtime model) :
    RuntimeLineRep (runtimeLineOfChain runtime) (Model.lineOfChain model) := by
  simpa [RuntimeChainRep, RuntimeLineRep, runtimeLineOfChain, Model.lineOfChain] using hrep

theorem Model.lineOfChain_bound {h : Model.ChainState} (hb : Model.ChainBound h) :
    Model.LineBound (Model.lineOfChain h) := by
  simpa [Model.ChainBound, Model.LineBound, Model.lineOfChain] using hb

theorem runtimeInitial_rep : RuntimeChainRep runtimeInitialChain Model.initial := by
  unfold RuntimeChainRep runtimeInitialChain Model.initial
  native_decide

theorem modelInitial_bound : Model.ChainBound Model.initial := by
  unfold Model.ChainBound Model.initial
  native_decide

theorem runtimeRecombineChain_rep
    {runtimeH : RuntimeChain} {modelH : Model.ChainState}
    {runtimeLeft runtimeRight : RuntimeLineState}
    {modelLeft modelRight : Model.LineState}
    (hh : RuntimeChainRep runtimeH modelH)
    (hl : RuntimeLineRep runtimeLeft modelLeft)
    (hr : RuntimeLineRep runtimeRight modelRight) :
    RuntimeChainRep (runtimeRecombineChain runtimeH runtimeLeft runtimeRight)
      { h0 := Model.u32 (modelH.h1 + modelLeft.c + modelRight.d)
        h1 := Model.u32 (modelH.h2 + modelLeft.d + modelRight.e)
        h2 := Model.u32 (modelH.h3 + modelLeft.e + modelRight.a)
        h3 := Model.u32 (modelH.h4 + modelLeft.a + modelRight.b)
        h4 := Model.u32 (modelH.h0 + modelLeft.b + modelRight.c) } := by
  rcases hh with ⟨hh0, hh1, hh2, hh3, hh4⟩
  rcases hl with ⟨hla, hlb, hlc, hld, hle⟩
  rcases hr with ⟨hra, hrb, hrc, hrd, hre⟩
  unfold runtimeRecombineChain RuntimeChainRep
  dsimp only
  constructor
  · simpa [hh1, hlc, hrd] using runtimeMask32_add3_toNat runtimeH.h1 runtimeLeft.c runtimeRight.d
  constructor
  · simpa [hh2, hld, hre] using runtimeMask32_add3_toNat runtimeH.h2 runtimeLeft.d runtimeRight.e
  constructor
  · simpa [hh3, hle, hra] using runtimeMask32_add3_toNat runtimeH.h3 runtimeLeft.e runtimeRight.a
  constructor
  · simpa [hh4, hla, hrb] using runtimeMask32_add3_toNat runtimeH.h4 runtimeLeft.a runtimeRight.b
  · simpa [hh0, hlb, hrc] using runtimeMask32_add3_toNat runtimeH.h0 runtimeLeft.b runtimeRight.c

theorem Model.chainBound_compress (data : ByteArray) (block : Nat)
    (h : Model.ChainState) : Model.ChainBound (Model.compress data block h) := by
  unfold Model.compress Model.ChainBound
  dsimp only
  repeat' apply And.intro (Nat.mod_lt _ (by norm_num [Model.modulus32]))
  exact Nat.mod_lt _ (by norm_num [Model.modulus32])

theorem runtimeCompressChain_rep (data : ByteArray) (block : Nat)
    (X : Fin 16 → UInt256) (runtime : RuntimeChain) (model : Model.ChainState)
    (hX : ∀ i, (X i).toNat = Model.blockWord data block i.val)
    (hrep : RuntimeChainRep runtime model) (hbound : Model.ChainBound model) :
    RuntimeChainRep (runtimeCompressChain X runtime) (Model.compress data block model) := by
  have hlineRep := runtimeLineOfChain_rep hrep
  have hlineBound := Model.lineOfChain_bound hbound
  have hleft := runtimePureLeftLine_rep data block 5 X _ _ (by decide)
    hX hlineRep hlineBound
  have hright := runtimePureRightLine_rep data block 5 X _ _ (by decide)
    hX hlineRep hlineBound
  unfold runtimeCompressChain Model.compress Model.runLeft Model.runRight
  exact runtimeRecombineChain_rep hrep hleft.1 hright.1

end Ripemd160
