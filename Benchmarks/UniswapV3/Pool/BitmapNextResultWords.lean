import Benchmarks.UniswapV3.Pool.BitmapNextReadWords
import Benchmarks.UniswapV3.Pool.ModularMultiplication
import Benchmarks.UniswapV3.Pool.TickSpacingModel
import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def bitmapNextDistance (compressed : Int) (lte : Bool) (masked : UInt256) : Int :=
  let bit := bitmapBitPos (bitmapNextPosition compressed lte)
  if lte then
    if masked = ⟨0⟩ then bit
    else normalizeInt (.uint ⟨8, by decide⟩) (bit - Int.ofNat (tickLogMsbCount masked))
  else normalizeInt (.uint ⟨8, by decide⟩)
    ((if masked = ⟨0⟩ then 255 else Int.ofNat (bitLsbCount masked)) - bit)

def bitmapNextDistanceRaw (compressed : Int) (lte : Bool) (masked : UInt256) : UInt256 :=
  let bit := bitmapPositionBitRaw (bitmapNextPosition compressed lte)
  if lte then
    if masked = ⟨0⟩ then UInt256.land (UInt256.ofNat 255) bit
    else UInt256.land (UInt256.ofNat 255) (UInt256.sub bit (UInt256.ofNat (tickLogMsbCount masked)))
  else UInt256.land (UInt256.ofNat 255)
    (UInt256.sub
      (if masked = ⟨0⟩ then UInt256.ofNat 255 else UInt256.ofNat (bitLsbCount masked)) bit)

def bitmapNextResultRaw (compressed : Int) (spacing : UInt256) (lte : Bool)
    (masked : UInt256) : UInt256 :=
  UInt256.mul (if lte then UInt256.sub (EVM.wordOfInt compressed)
      (bitmapNextDistanceRaw compressed lte masked)
    else (UInt256.ofNat 1 + EVM.wordOfInt compressed) +
      bitmapNextDistanceRaw compressed lte masked) spacing

theorem bitmapByteSubLeft (tick i : Int) :
    UInt256.land (UInt256.ofNat 255)
      (UInt256.sub (bitmapPositionBitRaw tick) (EVM.wordOfInt i)) =
      EVM.wordOfInt (normalizeInt (.uint ⟨8, by decide⟩) (bitmapBitPos tick - i)) := by
  rw [u256_land_comm, bitmapPositionBitRaw, ← wordOfInt_sub,
    ← wordOfInt_normalizeUint ⟨8, by decide⟩ _ (UInt256.ofNat 255) (by decide)]
  apply congrArg EVM.wordOfInt
  rw [← normalizeInt_sub_left, bitmapBitPos_tmod, bitmapBitPos_normalize]

theorem bitmapByteSubRight (tick i : Int) :
    UInt256.land (UInt256.ofNat 255)
      (UInt256.sub (EVM.wordOfInt i) (bitmapPositionBitRaw tick)) =
      EVM.wordOfInt (normalizeInt (.uint ⟨8, by decide⟩) (i - bitmapBitPos tick)) := by
  rw [u256_land_comm, bitmapPositionBitRaw, ← wordOfInt_sub,
    ← wordOfInt_normalizeUint ⟨8, by decide⟩ _ (UInt256.ofNat 255) (by decide)]
  apply congrArg EVM.wordOfInt
  rw [← normalizeInt_sub_right, bitmapBitPos_tmod, bitmapBitPos_normalize]

theorem bitmapNextDistance_word (compressed : Int) (lte : Bool) (masked : UInt256) :
    bitmapNextDistanceRaw compressed lte masked =
      EVM.wordOfInt (bitmapNextDistance compressed lte masked) := by
  cases lte <;> by_cases hz : masked = ⟨0⟩ <;>
    simp only [bitmapNextDistanceRaw, bitmapNextDistance, Bool.false_eq_true,
      Bool.true_eq, if_false, if_true, hz, ↓reduceIte]
  · exact bitmapByteSubRight _ 255
  · simpa only [wordOfInt_ofNat_eq] using bitmapByteSubRight
      (bitmapNextPosition compressed false) (Int.ofNat (bitLsbCount masked))
  · exact bitmapPositionBitClean _
  · simpa only [wordOfInt_ofNat_eq] using bitmapByteSubLeft
      (bitmapNextPosition compressed true) (Int.ofNat (tickLogMsbCount masked))

theorem bitmapByte_sint24 (i : Int) :
    normalizeInt (.sint ⟨24, by decide⟩) (normalizeInt (.uint ⟨8, by decide⟩) i) =
      normalizeInt (.uint ⟨8, by decide⟩) i := by
  have hb : 0 ≤ i % 256 ∧ i % 256 < 256 :=
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  apply normalizeSint_eq_self ⟨24, by decide⟩
  · change -(2 ^ 23 : Int) ≤ i % 256; omega
  · change i % 256 < (2 ^ 23 : Int); omega

theorem bitmapNextResult_distance (compressed spacing : Int) (lte : Bool) (masked : UInt256) :
    bitmapNextResult compressed spacing lte masked =
      normalizeInt (.sint ⟨24, by decide⟩)
        ((if lte then compressed - bitmapNextDistance compressed lte masked
          else compressed + 1 + bitmapNextDistance compressed lte masked) * spacing) := by
  have hm (i : Int) : normalizeInt (.sint ⟨24, by decide⟩)
        (normalizeInt (.sint ⟨24, by decide⟩) i * spacing) =
      normalizeInt (.sint ⟨24, by decide⟩) (i * spacing) := by
    simpa only [Int.mul_comm] using normalizeInt_mul_right (.sint ⟨24, by decide⟩) spacing i
  have ha (i j : Int) : normalizeInt (.sint ⟨24, by decide⟩)
        (normalizeInt (.sint ⟨24, by decide⟩) i + j) =
      normalizeInt (.sint ⟨24, by decide⟩) (i + j) := by
    simpa only [Int.add_comm] using normalizeInt_add_right (.sint ⟨24, by decide⟩) j i
  have hb := bitmapBitPos_bounds (bitmapNextPosition compressed lte)
  have hbit : normalizeInt (.sint ⟨24, by decide⟩)
      (bitmapBitPos (bitmapNextPosition compressed lte)) =
      bitmapBitPos (bitmapNextPosition compressed lte) :=
    normalizeSint_eq_self ⟨24, by decide⟩ _ (by change -(2 ^ 23 : Int) ≤ _; omega)
      (by change _ < (2 ^ 23 : Int); omega)
  cases lte <;> by_cases hz : masked = ⟨0⟩ <;>
    simp only [bitmapNextResult, bitmapNextDistance, Bool.false_eq_true, Bool.true_eq,
      if_false, if_true, hz, ↓reduceIte, bitmapByte_sint24, hbit, ha, hm]

theorem bitmapNextResultRaw_normalize (compressed spacing : Int) (spacingRaw : UInt256)
    (lte : Bool) (masked : UInt256)
    (hs : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat spacingRaw.toNat) = spacing) :
    normalizeInt (.sint ⟨24, by decide⟩)
      (Int.ofNat (bitmapNextResultRaw compressed spacingRaw lte masked).toNat) =
      bitmapNextResult compressed spacing lte masked := by
  have hr : bitmapNextResultRaw compressed spacingRaw lte masked =
      EVM.wordOfInt ((if lte then compressed - bitmapNextDistance compressed lte masked
        else compressed + 1 + bitmapNextDistance compressed lte masked) *
          Int.ofNat spacingRaw.toNat) := by
    cases lte <;> simp only [bitmapNextResultRaw, Bool.false_eq_true, Bool.true_eq,
      if_false, if_true, bitmapNextDistance_word, wordOfInt_mul, wordOfInt_add,
      wordOfInt_sub, wordOfInt_ofNat_toNat]
    · rw [u256_add_comm (UInt256.ofNat 1)]
      rfl
  rw [hr, normalizeInt_wordOfInt, ← normalizeInt_mul_right, hs, bitmapNextResult_distance]

end Benchmarks.UniswapV3.Pool
