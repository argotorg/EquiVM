import Benchmarks.UniswapV3.Pool.ConstructorModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def constructorFreeMem : ByteArray := writeWord ByteArray.empty 64 ⟨352⟩

def constructorOriginalWord (original : AccountAddress) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat original.val) ⟨96⟩

def constructorOriginalMem (original : AccountAddress) : ByteArray :=
  writeWord constructorFreeMem 128 (constructorOriginalWord original)

def constructorSelectorWord : UInt256 := UInt256.shiftLeft ⟨143668595⟩ ⟨228⟩

def constructorInputMem (original : AccountAddress) : ByteArray :=
  writeWord (constructorOriginalMem original) 352 constructorSelectorWord

def constructorOutputMem (original : AccountAddress) (out : ByteArray) : ByteArray :=
  out.write 0 (constructorInputMem original) 352 160

theorem constructorFreeMem_size : constructorFreeMem.size = 96 := by
  rw [constructorFreeMem, writeWord_sparse_size]
  rfl

theorem constructorOriginalMem_size (original : AccountAddress) :
    (constructorOriginalMem original).size = 160 := by
  rw [constructorOriginalMem, writeWord_sparse_size, constructorFreeMem_size]
  rfl

theorem constructorInputMem_size (original : AccountAddress) :
    (constructorInputMem original).size = 384 := by
  rw [constructorInputMem, writeWord_sparse_size, constructorOriginalMem_size]
  rfl

theorem constructorFreeMem_load64 : memLoad ⟨64⟩ constructorFreeMem = ⟨352⟩ := by
  apply loadedWord_of_read (by rw [constructorFreeMem_size]; decide)
  exact writeWord_sparse_read_back _ _ _

theorem constructorOriginalMem_read64 (original : AccountAddress) :
    (constructorOriginalMem original).readWithPadding 64 32 = (⟨352⟩ : UInt256).toByteArray := by
  rw [constructorOriginalMem, writeWord_sparse_read_preserved _ _ _ _
    (Or.inl ⟨by decide, by rw [constructorFreeMem_size]⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem constructorOriginalMem_load64 (original : AccountAddress) :
    memLoad ⟨64⟩ (constructorOriginalMem original) = ⟨352⟩ := by
  exact loadedWord_of_read (by rw [constructorOriginalMem_size]; decide)
    (constructorOriginalMem_read64 original)

theorem constructorInputMem_read64 (original : AccountAddress) :
    (constructorInputMem original).readWithPadding 64 32 = (⟨352⟩ : UInt256).toByteArray := by
  rw [constructorInputMem, writeWord_sparse_read_preserved _ _ _ _
    (Or.inl ⟨by decide, by rw [constructorOriginalMem_size]; decide⟩)]
  exact constructorOriginalMem_read64 original

theorem constructorInputMem_load64 (original : AccountAddress) :
    memLoad ⟨64⟩ (constructorInputMem original) = ⟨352⟩ := by
  exact loadedWord_of_read (by rw [constructorInputMem_size]; decide)
    (constructorInputMem_read64 original)

theorem constructorInputMem_read128 (original : AccountAddress) :
    (constructorInputMem original).readWithPadding 128 32 =
      (constructorOriginalWord original).toByteArray := by
  rw [constructorInputMem, writeWord_sparse_read_preserved _ _ _ _
    (Or.inl ⟨by decide, by rw [constructorOriginalMem_size]⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem constructorInputMem_calldata (original : AccountAddress) :
    (constructorInputMem original).readWithPadding 352 4 = constructorParameterCalldata := by
  change (writeWord _ 352 constructorSelectorWord).readWithPadding (352 + 0) 4 = _
  rw [writeWord_sparse_read_window _ _ 0 4 _ (by decide) (by decide) (by decide)]
  decide +kernel

theorem constructorCallOutput_eq (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) (hb : out.size < UInt256.size) :
    callOutputMem (constructorInputMem original) out ⟨352⟩ ⟨160⟩ =
      constructorOutputMem original out := by
  have hn : (⟨160⟩ : UInt256) ≤ UInt256.ofNat out.size := by
    change 160 ≤ (UInt256.ofNat out.size).toNat
    rw [ulit_toNat' _ hb]
    exact hlen
  simp only [callOutputMem, min, hn, if_true]
  rfl

theorem constructorOutputMem_size (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) : (constructorOutputMem original out).size = 512 := by
  rw [constructorOutputMem, copyWindow_size _ _ 0 352 160 (by decide) (by simpa using hlen)
    (by rw [constructorInputMem_size]; decide), constructorInputMem_size]
  rfl

theorem constructorOutputMem_read64 (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) :
    (constructorOutputMem original out).readWithPadding 64 32 = (⟨352⟩ : UInt256).toByteArray := by
  rw [constructorOutputMem, copyWindow_read_preserved _ _ 0 352 160 64 (by decide)
    (by simpa using hlen) (by rw [constructorInputMem_size]; decide)
    (by rw [constructorInputMem_size]; decide) (Or.inl (by decide))]
  exact constructorInputMem_read64 original

theorem constructorOutputMem_load64 (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) : memLoad ⟨64⟩ (constructorOutputMem original out) = ⟨352⟩ := by
  exact loadedWord_of_read (by rw [constructorOutputMem_size _ _ hlen]; decide)
    (constructorOutputMem_read64 original out hlen)

theorem constructorOutputMem_read128 (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) :
    (constructorOutputMem original out).readWithPadding 128 32 =
      (constructorOriginalWord original).toByteArray := by
  rw [constructorOutputMem, copyWindow_read_preserved _ _ 0 352 160 128 (by decide)
    (by simpa using hlen) (by rw [constructorInputMem_size]; decide)
    (by rw [constructorInputMem_size]; decide) (Or.inl (by decide))]
  exact constructorInputMem_read128 original

theorem constructorOutputMem_readParameter (original : AccountAddress) (out : ByteArray)
    (off : Nat) (hlen : 160 ≤ out.size) (hoff : off + 32 ≤ 160) :
    (constructorOutputMem original out).readWithPadding (352 + off) 32 =
      out.readWithPadding off 32 := by
  simpa only [constructorOutputMem, Nat.zero_add] using
    copyWindow_read_word out (constructorInputMem original) 0 352 160 off
    (by decide) (by simpa using hlen) (by rw [constructorInputMem_size]; decide) hoff

theorem constructorOutputMem_loadParameter (original : AccountAddress) (out : ByteArray)
    (off : Nat) (hlen : 160 ≤ out.size) (hoff : off + 32 ≤ 160) :
    memLoad (UInt256.ofNat (352 + off)) (constructorOutputMem original out) =
      calldataWord out off := by
  have hn : (UInt256.ofNat (352 + off)).toNat = 352 + off :=
    ulit_toNat' _ (by change 352 + off < 2 ^ 256; omega)
  apply loadedWord_of_read (by rw [hn, constructorOutputMem_size _ _ hlen]; omega)
  rw [hn, constructorOutputMem_readParameter _ _ _ hlen hoff,
    readWithPadding_eq_extract _ _ (by omega), calldataWord_bytes_at (by omega)]

theorem constructorOutputMem_load128 (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) :
    memLoad ⟨128⟩ (constructorOutputMem original out) = constructorOriginalWord original := by
  exact loadedWord_of_read (by rw [constructorOutputMem_size _ _ hlen]; decide)
    (constructorOutputMem_read128 original out hlen)

end Benchmarks.UniswapV3.Pool
