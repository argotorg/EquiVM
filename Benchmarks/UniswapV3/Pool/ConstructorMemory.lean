import Benchmarks.UniswapV3.Pool.ConstructorWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def constructorFieldsMem (original : AccountAddress) (out : ByteArray) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord (constructorOutputMem original out)
    256 (constructorFeeStored (calldataWord out 96)))
    224 (constructorAddressStored (calldataWord out 64)))
    192 (constructorAddressStored (calldataWord out 32)))
    160 (constructorAddressStored (calldataWord out 0))

def constructorTickMem (original : AccountAddress) (out : ByteArray) : ByteArray :=
  writeWord (constructorFieldsMem original out) 288 (constructorSpacingStored (calldataWord out 128))

def constructorFinalMem (original : AccountAddress) (out : ByteArray) : ByteArray :=
  writeWord (constructorTickMem original out) 320
    (constructorLiquidityStored (EVM.wordOfInt (spacingLiquidity (constructorSpacing out))))

def constructorStoredFields (original : AccountAddress) (out : ByteArray) : List (Nat × UInt256) :=
  [(128, constructorOriginalWord original),
   (160, constructorAddressStored (calldataWord out 0)),
   (192, constructorAddressStored (calldataWord out 32)),
   (224, constructorAddressStored (calldataWord out 64)),
   (256, constructorFeeStored (calldataWord out 96)),
   (288, constructorSpacingStored (calldataWord out 128)),
   (320, constructorLiquidityStored (EVM.wordOfInt (spacingLiquidity (constructorSpacing out))))]

theorem constructorFieldsMem_size (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) : (constructorFieldsMem original out).size = 512 := by
  simp only [constructorFieldsMem, writeWord_sparse_size, constructorOutputMem_size _ _ hlen]
  rfl

theorem constructorTickMem_size (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) : (constructorTickMem original out).size = 512 := by
  simp only [constructorTickMem, writeWord_sparse_size, constructorFieldsMem_size _ _ hlen]
  rfl

theorem constructorFinalMem_size (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) : (constructorFinalMem original out).size = 512 := by
  simp only [constructorFinalMem, writeWord_sparse_size, constructorTickMem_size _ _ hlen]
  rfl

theorem constructorFinalMem_read (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) (off : Nat) (value : UInt256)
    (hfield : (off, value) ∈ constructorStoredFields original out) :
    (constructorFinalMem original out).readWithPadding off 32 = value.toByteArray := by
  simp only [constructorStoredFields, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hfield
  rcases hfield with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [constructorFinalMem, constructorTickMem, constructorFieldsMem]
    rw [writeWord_sparse_read_preserved _ 320 128 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 288 128 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 160 128 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 192 128 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 224 128 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 256 128 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    exact constructorOutputMem_read128 original out hlen
  · simp only [constructorFinalMem, constructorTickMem, constructorFieldsMem]
    rw [writeWord_sparse_read_preserved _ 320 160 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 288 160 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    exact writeWord_sparse_read_back _ 160 _
  · simp only [constructorFinalMem, constructorTickMem, constructorFieldsMem]
    rw [writeWord_sparse_read_preserved _ 320 192 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 288 192 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 160 192 _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    exact writeWord_sparse_read_back _ 192 _
  · simp only [constructorFinalMem, constructorTickMem, constructorFieldsMem]
    rw [writeWord_sparse_read_preserved _ 320 224 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 288 224 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 160 224 _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 192 224 _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    exact writeWord_sparse_read_back _ 224 _
  · simp only [constructorFinalMem, constructorTickMem, constructorFieldsMem]
    rw [writeWord_sparse_read_preserved _ 320 256 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 288 256 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 160 256 _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 192 256 _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    rw [writeWord_sparse_read_preserved _ 224 256 _ (Or.inr ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    exact writeWord_sparse_read_back _ 256 _
  · simp only [constructorFinalMem, constructorTickMem, constructorFieldsMem]
    rw [writeWord_sparse_read_preserved _ 320 288 _ (Or.inl ⟨by decide, by
      simp only [writeWord_sparse_size, constructorOutputMem_size _ _ hlen]; omega⟩)]
    exact writeWord_sparse_read_back _ 288 _
  · simp only [constructorFinalMem, constructorTickMem, constructorFieldsMem]
    exact writeWord_sparse_read_back _ 320 _

theorem constructorFinalMem_load (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) (off : Nat) (value : UInt256)
    (hfield : (off, value) ∈ constructorStoredFields original out) :
    memLoad (UInt256.ofNat off) (constructorFinalMem original out) = value := by
  have hoff : off + 32 ≤ 512 := by
    simp only [constructorStoredFields, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hfield
    rcases hfield with h | h | h | h | h | h | h <;> omega
  have hn : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by change off < 2 ^ 256; omega)
  apply loadedWord_of_read (by rw [hn, constructorFinalMem_size _ _ hlen]; exact hoff)
  rw [hn]
  exact constructorFinalMem_read original out hlen off value hfield

end Benchmarks.UniswapV3.Pool
