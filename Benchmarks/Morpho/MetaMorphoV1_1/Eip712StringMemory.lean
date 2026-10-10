import Benchmarks.Morpho.MetaMorphoV1_1.ShortStringMemory
import Benchmarks.Morpho.MetaMorphoV1_1.FallbackStringMemory
import Benchmarks.Morpho.MetaMorphoV1_1.FallbackStringAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.Eip712StringAllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.StringBuffer

/-! Cursor and memory invariants shared by the two domain-string representations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def domainStringEnd (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (free : Nat) : Nat :=
  if domainStringImmutable v version = ⟨255⟩ then
    free + 32 + paddedSize (domainStringBytes v version evm).size
  else free + 64

theorem domainStringEnd_ge (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (free : Nat) : free + 32 ≤ domainStringEnd evm v version free := by
  unfold domainStringEnd
  split <;> omega

theorem domainStringEnd_bound (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (free : Nat) (hfree : free < 2 ^ 64) : domainStringEnd evm v version free < UInt256.size := by
  have hb := domainStringBytes_bound evm v version
  unfold domainStringEnd paddedSize
  split <;> change _ < 2 ^ 256 <;> omega

theorem domainStringNextCursor (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (free : Nat) :
    nextCursor (UInt256.ofNat free)
      (domainStringSize (domainStringImmutable v version) (domainStringBytes v version evm)) =
      UInt256.ofNat (domainStringEnd evm v version free) := by
  by_cases h : domainStringImmutable v version = ⟨255⟩
  · simp only [domainStringSize, domainStringEnd, domainStringBytes, if_pos h]
    rw [storageStringBytes_size, stringSourceNextCursorAt free _ (storageStringLength_lt _)]
    rfl
  · simp only [domainStringSize, domainStringEnd, if_neg h]
    exact ofNat_add_words _ _

theorem domainStringAllocationFits (evm : State) (v : MetaMorphoV1_1Immutables)
    (version : Bool) (free : Nat) (hfree : free < 2 ^ 64) :
    allocationFits (UInt256.ofNat free)
      (domainStringSize (domainStringImmutable v version) (domainStringBytes v version evm)) ↔
      domainStringEnd evm v version free < 2 ^ 64 := by
  rw [allocationFits, domainStringNextCursor,
    UInt256.toNat_ofNat_of_lt (domainStringEnd_bound evm v version free hfree),
    UInt256.toNat_ofNat_of_lt (lt_trans hfree (by decide))]
  have := domainStringEnd_ge evm v version free
  omega

theorem domainStringEnd_covers (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (free : Nat) (hvalid : domainStringValid v version evm) :
    free + 32 + paddedSize (domainStringBytes v version evm).size ≤
      domainStringEnd evm v version free := by
  unfold domainStringEnd
  split
  · rfl
  · rename_i h
    simp only [domainStringValid, if_neg h] at hvalid
    simp only [domainStringBytes, if_neg h, shortStringBytes_size _ hvalid, paddedSize]
    have hl : (shortStringLength (domainStringImmutable v version)).toNat ≤ 31 := hvalid
    omega

theorem shortStringMemory_buffer (mem calldata : ByteArray) (free : Nat) (word : UInt256)
    (hfree : free < UInt256.size) (hvalid : shortStringValid word) :
    StringBuffer (shortStringMemory mem calldata free word) free (shortStringBytes word) := by
  have hl : (shortStringLength word).toNat ≤ 31 := hvalid
  refine ⟨?_, ?_, ?_⟩
  · rw [shortStringMemory_size, shortStringBytes_size word hvalid]
    unfold paddedSize
    omega
  · rw [shortStringMemory_length mem calldata free word hfree,
      shortStringBytes_size word hvalid]
    exact (u256_ofNat_toNat _).symm
  · rw [shortStringBytes_size word hvalid]
    exact shortStringMemory_read mem calldata free word hvalid

theorem fallbackStringMemory_buffer (evm : State) (mem : ByteArray) (base : UInt256)
    (free : Nat) (hlo : 96 ≤ free) (hfree : free < UInt256.size)
    (hvalid : storageStringValid (storageStringHeader evm base)) :
    StringBuffer (fallbackStringMemory evm.executionEnv evm.accountMap mem base
      (storageStringHeader evm base) free) free (storageStringBytes evm base) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [storageStringBytes_size]
    exact fallbackStringMemory_size _ _ _ _ _ _ hvalid
  · rw [fallbackStringMemory_length _ _ _ _ _ _ hlo hfree, storageStringBytes_size]
    exact (u256_ofNat_toNat _).symm
  · rw [storageStringBytes_size]
    exact fallbackStringMemory_read evm mem base free hvalid

-- LIBRARY CANDIDATE: writing the free-memory cursor preserves an allocated string.
theorem StringBuffer.writeFree {mem bytes : ByteArray} {ptr : Nat}
    (buffer : StringBuffer mem ptr bytes) (next : UInt256)
    (hlo : 96 ≤ ptr) (hfit : ptr < UInt256.size) :
    StringBuffer (writeWord mem 64 next) ptr bytes := by
  exact buffer.preserve (memoryPrefix_sparse_writeWord mem 64
    (ptr + 32 + paddedSize bytes.size) next (.inr (by decide))) hlo hfit (le_refl _)

end Benchmarks.Morpho.MetaMorphoV1_1
