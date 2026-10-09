import Benchmarks.CompoundIII.Comet.MappingGetter
import Benchmarks.CompoundIII.Comet.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def low128 (w : UInt256) : UInt256 := UInt256.land w (UInt256.ofNat (2 ^ 128 - 1))

def high128 (w : UInt256) : UInt256 := UInt256.shiftRight w ⟨128⟩

theorem low128_lt (w : UInt256) : (low128 w).toNat < 2 ^ 128 :=
  u256LandMaskToNatLtOfToNat w _ rfl

theorem high128_lt (w : UInt256) : (high128 w).toNat < 2 ^ 128 := by
  simp [high128, UInt256.shiftRight, UInt256.toNat, Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul w.val.isLt

theorem low128_clean (w : UInt256) (hw : w.toNat < 2 ^ 128) : low128 w = w :=
  u256LandMaskCleanOfToNat w _ rfl hw

theorem mask128Clean (w : UInt256) (hw : w.toNat < 2^128) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1)) w = w := by
  rw [u256_land_comm]
  exact low128_clean w hw

theorem low128_load (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
      { slot := slot, offset := 0, size := ⟨16, by decide⟩, hbound := by decide,
        type := .int (.uint ⟨128, by decide⟩) } =
      .int (low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat := by
  exact storageLocLoad_uint_offset0 evm slot ⟨16, by decide⟩ ⟨128, by decide⟩
    rfl (by decide)

theorem high128_load (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
      { slot := slot, offset := ⟨16, by decide⟩, size := ⟨16, by decide⟩, hbound := by decide,
        type := .int (.uint ⟨128, by decide⟩) } =
      .int (high128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat := by
  rw [storageLocLoad_uint_offset evm slot ⟨16, by decide⟩ ⟨16, by decide⟩
    ⟨128, by decide⟩ rfl (by decide) (by decide)]
  have hdiv : UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
      (UInt256.ofNat (256 ^ 16)) =
      high128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) := by
    apply u256_inj
    simp [high128, UInt256.shiftRight, UInt256.div, UInt256.toNat, Fin.shiftRight_val,
      Nat.shiftRight_eq_div_pow, UInt256.ofNat]
    rfl
  rw [hdiv]
  change Value.int (low128 (high128 _)).toNat = _
  rw [low128_clean _ (high128_lt _)]

-- GENERALIZES Reasoning.ABIViews.uint256PairReturnEncoding to elementary return types.
theorem scalarPairReturnEncoding {t₁ t₂ : ElemType} {v₁ v₂ : Value} {w₁ w₂ : UInt256}
    (h₁ : encodeABIValue? (.elem t₁) v₁ = some (EVM.Word.toBytesBE w₁))
    (h₂ : encodeABIValue? (.elem t₂) v₂ = some (EVM.Word.toBytesBE w₂)) :
    encodeReturnValues? [.elem t₁, .elem t₂] [v₁, v₂] =
      some (w₁.toByteArray ++ w₂.toByteArray) := by
  simp only [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, bind, Option.bind, encodeABIValuesFrom?, h₁, h₂,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray, ← word_toBytesBE_toByteArray_eq_toByteArray]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

-- LIBRARY CANDIDATE: elementary encoding of a bounded unsigned word.
theorem uintWordEncoding (width : ABI.BitWidth) (w : UInt256)
    (hn : width.val ≠ 0) (hw : w.toNat < EVM.twoPow width.val) :
    encodeABIValue? (.elem (.int (.uint width))) (.int w.toNat) =
      some (EVM.Word.toBytesBE w) := by
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [encodeABIValue?, encodeABIWord?, hn, hw, hword]

-- LIBRARY CANDIDATE: ABI return of two words after an arbitrary 96-byte scratch area.
theorem scratchPairReturnData {mem : ByteArray} (a b : UInt256) (hmem : mem.size = 96) :
    (b.toByteArray.write 0 (solcScratchReturnMem mem a) 160 32).readWithPadding 128 64 =
      a.toByteArray ++ b.toByteArray := by
  have hfirst := solcScratchReturnMem_size a hmem
  have hsecond : (b.toByteArray.write 0 (solcScratchReturnMem mem a) 160 32).size = 192 := by
    exact toByteArray_write32_size_of_ge _ b 160 160 192 hfirst (by decide)
      (lt_usize _ (by norm_num)) (by decide)
  rw [show (64 : Nat) = 32 + 32 by rfl,
    byteArray_readWithPadding_split_unbounded _ 128 32 32 (by decide) (by decide)
      (by rw [hsecond]),
    write32_read_below _ _ 160 128 (by rw [toByteArray_size]) (by omega) (by decide),
    solcScratchReturnMem_read128 a hmem,
    toByteArray_write32_read_back _ b 160 (by omega)]

end Benchmarks.CompoundIII.Comet
