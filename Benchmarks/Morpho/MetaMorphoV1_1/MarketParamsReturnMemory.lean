import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory

/-! Return-buffer reads and memory facts for the five decoded market-parameter words. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem marketParamsOutputMem_long (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hl : 160 ≤ out.size) (hh : out.size < UInt256.size) :
    marketParamsOutputMem mem ptr out = out.write 0 mem ptr.toNat 160 :=
  fixedReturnBuffer_long mem ptr out hl hh

theorem marketParamsOutputMem_size {mem out : ByteArray} {ptr : UInt256}
    (hin : ptr.toNat ≤ mem.size) (hl : 160 ≤ out.size) (hh : out.size < UInt256.size) :
    (marketParamsOutputMem mem ptr out).size = max mem.size (ptr.toNat + 160) :=
  fixedReturnBuffer_size (by decide) hin hl hh

theorem marketParamsOutputMem_load {mem out : ByteArray} {ptr : UInt256} {off : Nat}
    (hin : ptr.toNat ≤ mem.size) (hl : 160 ≤ out.size) (hh : out.size < UInt256.size)
    (hp : ptr.toNat + 160 < UInt256.size) (hoff : off + 32 ≤ 160) :
    memLoad (ptr + UInt256.ofNat off) (marketParamsOutputMem mem ptr out) =
      calldataWord out off :=
  fixedReturnBuffer_load hin hl hh hp hoff

theorem marketParamsReservedMem_size (mem : ByteArray) (ptr : UInt256) :
    (marketParamsReservedMem mem ptr).size = max mem.size 96 := by
  simp only [marketParamsReservedMem, writeWord_sparse_size, max_self, max_assoc]

theorem marketParamsReservedMem_free (mem : ByteArray) (ptr : UInt256) :
    memLoad ⟨64⟩ (marketParamsReservedMem mem ptr) =
      nextCursor (nextCursor ptr ⟨160⟩) ⟨160⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem marketParamsReservedMem_load {mem out : ByteArray} {ptr : UInt256} {off : Nat}
    (hlo : 96 ≤ ptr.toNat) (hmem : ptr.toNat + 160 ≤ mem.size)
    (hp : ptr.toNat + 160 < UInt256.size) (hoff : off + 32 ≤ 160)
    (hread : memLoad (ptr + UInt256.ofNat off) mem = calldataWord out off) :
    memLoad (ptr + UInt256.ofNat off) (marketParamsReservedMem mem ptr) =
      calldataWord out off := by
  rw [marketParamsReservedMem,
    wordWindowRead_freeWrite _ hlo (by rw [writeWord_sparse_size]; omega) hp hoff,
    wordWindowRead_freeWrite _ hlo hmem hp hoff]
  exact hread

def marketParamsCopyMem (mem : ByteArray) (dst : Nat) (out : ByteArray) : ByteArray :=
  structReturnMemory mem dst out 5

theorem marketParamsCopyMem_size (mem : ByteArray) (dst : Nat) (out : ByteArray) :
    (marketParamsCopyMem mem dst out).size = max mem.size (dst + 160) :=
  structReturnMemory_size mem dst out (by decide)

theorem marketParamsCopyMem_free {mem out : ByteArray} {dst : Nat}
    (hmem : 96 ≤ mem.size) (hdst : 96 ≤ dst) :
    memLoad ⟨64⟩ (marketParamsCopyMem mem dst out) = memLoad ⟨64⟩ mem :=
  structReturnMemory_free hmem hdst

theorem marketParamsCopyMem_field (mem : ByteArray) (dst : Nat) (out : ByteArray)
    (i : Nat) (hi : i < 5) (hfit : dst + 160 < UInt256.size) :
    memLoad (UInt256.ofNat (dst + 32 * i)) (marketParamsCopyMem mem dst out) =
      calldataWord out (32 * i) :=
  structReturnMemory_field mem dst out i hi hfit

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
