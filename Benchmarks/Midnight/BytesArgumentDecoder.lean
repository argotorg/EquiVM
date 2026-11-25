import Benchmarks.Midnight.BytesCalldataMemory
import Benchmarks.Midnight.CalldataArgumentSlice

variable {fork : Ethereum.Fork}

/-! Materialized byte strings addressed by a top-level calldata argument. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem decodeCalldataBytes_eq_at {bytes : ByteArray} {slot : Nat}
    (ho : (calldataWord bytes slot).toNat < 2^64) :
    decodeCalldataBytes bytes slot =
      decodeBytesAt bytes (4 + (calldataWord bytes slot).toNat) := by
  simp only [decodeCalldataBytes, ho, if_true, CalldataSliceValid,
    UInt256.toNat_ofNat_of_lt (show 4 + (calldataWord bytes slot).toNat < UInt256.size by
      change _ < 2^256; omega), calldataSliceStride, Nat.one_mul, decodeBytesAt]

theorem decodeCalldataBytes_offset {bytes data : ByteArray} {slot : Nat}
    (hd : decodeCalldataBytes bytes slot = some data) :
    (calldataWord bytes slot).toNat < 2^64 := by
  unfold decodeCalldataBytes at hd
  dsimp only at hd
  split at hd
  · assumption
  · cases hd

theorem decodeCalldataBytes_success_at {bytes data : ByteArray} {slot : Nat}
    (hd : decodeCalldataBytes bytes slot = some data) :
    decodeBytesAt bytes (4 + (calldataWord bytes slot).toNat) = some data := by
  rwa [decodeCalldataBytes_eq_at (decodeCalldataBytes_offset hd)] at hd

-- LIBRARY CANDIDATE: a materialized bytes decoder with its top-level offset already checked.
theorem midnightBytesArgumentDecoder {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C slot : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (ho : (calldataWord I.calldata slot).toNat < 2^64)
    (hptr : ptr.toNat < 2^64) (hsize : I.calldata.size < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19043⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata slot) ::
        UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    ((∀ data, decodeCalldataBytes I.calldata slot = some data →
        ¬ ptr.toNat + returnDataAllocation data.size < 2^64) ∧ RDrev fork midnightBytecode g s0) ∨
    (∃ data, decodeCalldataBytes I.calldata slot = some data ∧
      ptr.toNat + returnDataAllocation data.size < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding (credit + 3 * ((data.size + 31) / 32))
          (bytesCalldataMemory mem I.calldata ptr
            (4 + (calldataWord I.calldata slot).toNat)) aw' C' ∧
        RD fork midnightBytecode I g s0 ret (ptr :: R)
          (bytesCalldataMemory mem I.calldata ptr
            (4 + (calldataWord I.calldata slot).toNat)) aw' rdata σ k' C') := by
  have hh := calldataArgumentHead_toNat ho
  change (UInt256.ofNat 4 + calldataWord I.calldata slot).toNat = _ at hh
  have hd := midnightBytesCalldataDecoder_funded hstack (by rw [hh]; omega)
    hptr hsize hfree hvalid ha rd
  rwa [hh, ← decodeCalldataBytes_eq_at ho] at hd

end Benchmarks.Midnight
