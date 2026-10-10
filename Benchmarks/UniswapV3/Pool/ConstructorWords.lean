import Benchmarks.UniswapV3.Pool.ConstructorInputMemory
import Benchmarks.UniswapV3.Pool.ShiftCleanup
import Benchmarks.UniswapV3.Pool.TickSpacingWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def constructorAddressStored (word : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftLeft word ⟨96⟩)
    (UInt256.lnot (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨96⟩) ⟨1⟩))

def constructorFeeStored (word : UInt256) : UInt256 :=
  UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨232⟩) ⟨1⟩))
    (UInt256.shiftLeft word ⟨232⟩)

def constructorSpacingStored (word : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ word)) ⟨232⟩

def constructorLiquidityStored (word : UInt256) : UInt256 :=
  UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨128⟩) ⟨1⟩))
    (UInt256.shiftLeft word ⟨128⟩)

theorem constructorOriginalWord_decode (original : AccountAddress) :
    UInt256.shiftRight (constructorOriginalWord original) ⟨96⟩ = EVM.word original.val :=
  addressWord_shiftLeft96_shiftRight96 original

theorem constructorAddressStored_decode (word : UInt256) :
    UInt256.shiftRight (constructorAddressStored word) ⟨96⟩ =
      EVM.word (AccountAddress.ofNat word.toNat).val := by
  rw [constructorAddressStored, wordShiftLeft_highMask _ _ _ (by decide) (by decide),
    wordShiftLeftRight_mask word ⟨96⟩ solcAddrMask (by decide) (by decide),
    ← word_of_addressOfNat_eq_mask]

theorem constructorFeeStored_decode (out : ByteArray) :
    UInt256.shiftRight (constructorFeeStored (calldataWord out 96)) ⟨232⟩ =
      EVM.wordOfInt (constructorFee out) := by
  rw [constructorFeeStored, u256_land_comm,
    wordShiftLeft_highMask _ _ _ (by decide) (by decide),
    wordShiftLeftRight_mask _ ⟨232⟩ ⟨16777215⟩ (by decide) (by decide)]
  unfold constructorFee
  rw [wordOfInt_normalizeUint ⟨24, by decide⟩ _ ⟨16777215⟩ (by decide), wordOfInt_ofNat_toNat]

theorem constructorSpacingStored_decode (out : ByteArray) :
    UInt256.shiftRight (constructorSpacingStored (calldataWord out 128)) ⟨232⟩ =
      EVM.wordOfInt (constructorUnsignedSpacing out) := by
  have hs : UInt256.signextend ⟨2⟩ (calldataWord out 128) =
      EVM.wordOfInt (constructorSpacing out) := spacingWord_clean _ _ rfl
  rw [constructorSpacingStored, signextend_idem ⟨24, by decide⟩ _ _ (by decide) (by decide),
    hs,
    wordShiftLeftRight_mask _ ⟨232⟩ ⟨16777215⟩ (by decide) (by decide)]
  exact (wordOfInt_normalizeUint ⟨24, by decide⟩ (constructorSpacing out) ⟨16777215⟩
    (by decide)).symm

theorem constructorLiquidityStored_decode (out : ByteArray) :
    UInt256.shiftRight
      (constructorLiquidityStored (EVM.wordOfInt (spacingLiquidity (constructorSpacing out))))
      ⟨128⟩ = EVM.wordOfInt (spacingLiquidity (constructorSpacing out)) := by
  rw [constructorLiquidityStored, u256_land_comm,
    wordShiftLeft_highMask _ _ _ (by decide) (by decide),
    wordShiftLeftRight_mask _ ⟨128⟩ (UInt256.ofNat (2 ^ 128 - 1)) (by decide) (by decide),
    ← wordOfInt_normalizeUint ⟨128, by decide⟩ _ (UInt256.ofNat (2 ^ 128 - 1)) (by decide)]
  have hb := spacingLiquidity_bounds (constructorSpacing out)
  rw [normalizeInt_uint_eq_self ⟨128, by decide⟩ _ hb.1 hb.2]

end Benchmarks.UniswapV3.Pool
