import Benchmarks.WETH9.StringLayout
import Reasoning.Storage
import Reasoning.EVMWord

/-!
# WETH9 constructor — trusted keccak values + foundational storage/arithmetic lemmas

Two trusted keccak-value axioms (the compact-string data base slots `keccak(0)` / `keccak(1)`),
the `clearDataWordsForwardFrom` last-store peel lemma used by the symbolic clear loop, the
`∀S` identity between the creation bytecode's mask arithmetic and the total 0.5.16 length decode,
and the no-overflow bound that keeps the clear-loop cursor `keccak(slot) + i` from wrapping.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.WETH9

set_option maxRecDepth 4000000

/-! ## Trusted keccak data base slots (the ONLY new axioms) -/

/-- `keccak256(bytes32(0))` — the compact-string data words base slot for storage slot 0 (`name`). -/
axiom weth9DataBaseSlot0 :
    Solm.solidityBytesDataBaseSlot ⟨0⟩ =
      (⟨0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563⟩ : UInt256)

/-- `keccak256(bytes32(1))` — the compact-string data words base slot for storage slot 1 (`symbol`). -/
axiom weth9DataBaseSlot1 :
    Solm.solidityBytesDataBaseSlot ⟨1⟩ =
      (⟨0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6⟩ : UInt256)

/-! ## Small `UInt256` additive helpers (no `AddCommMagma UInt256` instance is available) -/

theorem uadd_comm (a b : UInt256) : a + b = b + a := by
  apply u256_inj; rw [uadd_toNat, uadd_toNat, Nat.add_comm]

theorem uadd_assoc (a b c : UInt256) : a + b + c = a + (b + c) := by
  apply u256_inj
  rw [uadd_toNat, uadd_toNat, uadd_toNat, uadd_toNat, Nat.mod_add_mod, Nat.add_mod_mod,
    Nat.add_assoc]

/-! ## `clearDataWordsForwardFrom` last-store peel -/

/-- General append/split for the forward zeroing fold: running `fuel + tail` clears is running
    `tail` more clears from the advanced cursor after the first `fuel`. -/
theorem clearDataWordsForwardFrom_append_gen (owner : AccountAddress) (base : UInt256) :
    ∀ (fuel : Nat) (τ : AccountMap) (idx : UInt256) (tail : Nat),
      clearDataWordsForwardFrom owner τ base idx (fuel + tail) =
        clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base idx fuel) base
          (UInt256.ofNat fuel + idx) tail
  | 0, τ, idx, tail => by
      simp only [Nat.zero_add, clearDataWordsForwardFrom]
      rw [show (UInt256.ofNat 0 + idx) = idx from by
        apply u256_inj; rw [uadd_toNat]
        simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add]
        exact Nat.mod_eq_of_lt idx.val.isLt]
  | fuel + 1, τ, idx, tail => by
      have key : fuel + 1 + tail = (fuel + tail) + 1 := by omega
      rw [key, clearDataWordsForwardFrom,
        clearDataWordsForwardFrom_append_gen owner base fuel
          (sstoreAccountMap owner τ (base + idx) ⟨0⟩) ((⟨1⟩ : UInt256) + idx) tail]
      conv_rhs => rw [clearDataWordsForwardFrom]
      rw [show UInt256.ofNat (fuel + 1) + idx = UInt256.ofNat fuel + ((⟨1⟩ : UInt256) + idx) from by
        rw [← u256_one_add_ofNat, uadd_comm (⟨1⟩ : UInt256) (UInt256.ofNat fuel), uadd_assoc]]

/-- Peel the final store off a `⟨0⟩`-based clear run: `n+1` clears equal `n` clears followed by a
    single `sstore` of `⟨0⟩` at `base + n`. -/
theorem clearDataWordsForwardFrom_append (owner : AccountAddress) (τ : AccountMap)
    (base : UInt256) (n : Nat) :
    clearDataWordsForwardFrom owner τ base ⟨0⟩ (n + 1) =
      sstoreAccountMap owner (clearDataWordsForwardFrom owner τ base ⟨0⟩ n)
        (base + UInt256.ofNat n) ⟨0⟩ := by
  rw [clearDataWordsForwardFrom_append_gen owner base n τ ⟨0⟩ 1]
  rw [show (UInt256.ofNat n + (⟨0⟩ : UInt256)) = UInt256.ofNat n from by
    apply u256_inj; rw [uadd_toNat]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero]
    exact Nat.mod_eq_of_lt (UInt256.ofNat n).val.isLt]
  rw [clearDataWordsForwardFrom, clearDataWordsForwardFrom]

/-! ## The mask-arithmetic length decode agrees with the total 0.5.16 decode -/

/-- The creation bytecode's inline length computation (creation.hex pc 125–142):
    `(S & (iszero(S&1)·256 − 1)) / 2`. -/
def weth9EvmLenWord (S : UInt256) : UInt256 :=
  UInt256.div
    (UInt256.land
      (UInt256.sub (UInt256.mul ⟨256⟩ (UInt256.isZero (UInt256.land ⟨1⟩ S))) ⟨1⟩) S)
    ⟨2⟩

/-- The total 0.5.16 decode's decoded length word (before `.toNat`). -/
def weth9DecodeLenWord (S : UInt256) : UInt256 :=
  if UInt256.land S ⟨1⟩ = ⟨0⟩ then UInt256.land (UInt256.div S ⟨2⟩) ⟨127⟩
  else UInt256.div S ⟨2⟩

theorem weth9DecodeBytesLengthHeader_eq (S : UInt256) :
    weth9DecodeBytesLengthHeader S = .ok (weth9DecodeLenWord S).toNat := rfl

theorem uland_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj; rw [uland_toNat, uland_toNat, Nat.and_comm]

/-- `∀S` identity: the mask arithmetic equals the total decode's length word. -/
theorem weth9EvmLenWord_eq (S : UInt256) : weth9EvmLenWord S = weth9DecodeLenWord S := by
  unfold weth9EvmLenWord weth9DecodeLenWord
  rw [uland_comm ⟨1⟩ S]
  by_cases h : UInt256.land S ⟨1⟩ = ⟨0⟩
  · rw [h, if_pos rfl]
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from rfl]
    rw [show UInt256.mul ⟨256⟩ ⟨1⟩ = (⟨256⟩ : UInt256) from by apply u256_inj; rw [u256_mul_toNat]; decide]
    rw [show UInt256.sub ⟨256⟩ ⟨1⟩ = (⟨255⟩ : UInt256) from by apply u256_inj; rw [usub_toNat (by decide)]; decide]
    apply u256_inj
    rw [udiv_toNat, uland_toNat, uland_toNat, udiv_toNat]
    have heven : S.toNat % 2 = 0 := by
      have := congrArg UInt256.toNat h
      rw [uland_toNat] at this
      simpa [show (⟨1⟩ : UInt256).toNat = 1 from rfl, Nat.and_one_is_mod,
        show (⟨0⟩ : UInt256).toNat = 0 from rfl] using this
    simp only [show (⟨255⟩ : UInt256).toNat = 255 from rfl,
      show (⟨2⟩ : UInt256).toNat = 2 from rfl,
      show (⟨127⟩ : UInt256).toNat = 127 from rfl]
    rw [Nat.and_comm 255 S.toNat,
      show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rw [if_neg h]
    have h1 : UInt256.land S ⟨1⟩ = (⟨1⟩ : UInt256) := by
      apply u256_inj
      rw [uland_toNat, show (⟨1⟩ : UInt256).toNat = 1 from rfl, Nat.and_one_is_mod]
      have hne : S.toNat % 2 ≠ 0 := by
        intro hz; apply h; apply u256_inj
        rw [uland_toNat, show (⟨1⟩ : UInt256).toNat = 1 from rfl, Nat.and_one_is_mod,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        exact hz
      omega
    rw [h1]
    rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from rfl]
    rw [show UInt256.mul ⟨256⟩ ⟨0⟩ = (⟨0⟩ : UInt256) from by apply u256_inj; rw [u256_mul_toNat]; decide]
    congr 1
    apply u256_inj
    rw [uland_toNat, usub_toNat_underflow (by decide : (⟨0⟩ : UInt256).toNat < (⟨1⟩ : UInt256).toNat),
      Nat.and_comm]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨1⟩ : UInt256).toNat = 1 from rfl,
      Nat.add_zero]
    rw [show UInt256.size - 1 = 2 ^ 256 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt S.val.isLt

/-! ## Length / word-count bounds and the clear-loop no-overflow -/

theorem weth9DecodeLenWord_lt (S : UInt256) : (weth9DecodeLenWord S).toNat < 2 ^ 255 := by
  unfold weth9DecodeLenWord
  by_cases h : UInt256.land S ⟨1⟩ = ⟨0⟩
  · rw [if_pos h, uland_toNat, udiv_toNat]
    have hle : (S.toNat / (⟨2⟩ : UInt256).toNat) &&& (⟨127⟩ : UInt256).toNat
        ≤ (⟨127⟩ : UInt256).toNat := Nat.and_le_right
    rw [show (⟨127⟩ : UInt256).toNat = 127 from rfl] at hle ⊢
    omega
  · rw [if_neg h, udiv_toNat, show (⟨2⟩ : UInt256).toNat = 2 from rfl]
    have hlt : S.toNat < UInt256.size := S.val.isLt
    have hsize : UInt256.size = 2 ^ 256 := rfl
    omega

theorem weth9OldWords_lt (S : UInt256) :
    solidityBytesDataWordCount (weth9DecodeLenWord S).toNat < 2 ^ 251 := by
  unfold solidityBytesDataWordCount
  have := weth9DecodeLenWord_lt S
  omega

/-- Clear-loop no-overflow: for `name`/`symbol` slots the keccak-data base slot plus the entire
    cleared-word count stays below `2^256`. -/
theorem weth9NoOverflow (slot : UInt256) (hslot : slot = ⟨0⟩ ∨ slot = ⟨1⟩) (S : UInt256) :
    (Solm.solidityBytesDataBaseSlot slot).toNat +
      solidityBytesDataWordCount (weth9DecodeLenWord S).toNat < UInt256.size := by
  have hw := weth9OldWords_lt S
  have hsize : UInt256.size = 2 ^ 256 := rfl
  rcases hslot with h | h
  · subst h; rw [weth9DataBaseSlot0]
    rw [show (⟨0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563⟩ : UInt256).toNat
        = 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563 from rfl]
    omega
  · subst h; rw [weth9DataBaseSlot1]
    rw [show (⟨0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6⟩ : UInt256).toNat
        = 0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6 from rfl]
    omega

end Benchmarks.WETH9
