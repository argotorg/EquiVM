import Benchmarks.EAS.Attester.MultiRevokeHeap
import Benchmarks.EAS.Attester.PairRequestsABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def multiRevokeSchemas (cd : ByteArray) (i : Nat) : UInt256 :=
  calldataWord cd (arrayDataNat cd 4 + 32 * i)

def multiRevokeCounts (cd : ByteArray) (i : Nat) : Nat :=
  (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat

def multiRevokeValues (cd : ByteArray) (i j : Nat) : UInt256 × UInt256 :=
  (calldataWord cd ((rowData cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 * j), ⟨0⟩)

def multiRevokeRequests (cd : ByteArray) : Value :=
  .array (pairRequestsValues (multiRevokeSchemas cd) (multiRevokeCounts cd)
    (multiRevokeValues cd) 0 (arrayCount cd 4))

def multiRevokeSelectorWord : UInt256 :=
  UInt256.ofNat 34700723785909278827545364893952542206761801622036869180408675228056652087296

def multiRevokeEncodedMemory (cd : ByteArray) : ByteArray :=
  pairRequestsABIMemory (writeWord (multiRevokeBuiltMemory cd) (multiRevokeBuiltFree cd)
    multiRevokeSelectorWord) (multiRevokeBuiltFree cd + 4) (arrayCount cd 4)
    (multiRevokeSchemas cd) (multiRevokeCounts cd) (multiRevokeValues cd)

def multiRevokeEncodedEnd (cd : ByteArray) : Nat :=
  pairRequestsABIEnd (multiRevokeBuiltFree cd + 4) (arrayCount cd 4) (multiRevokeCounts cd)

theorem multiRevokeEncodedEnd_bounds {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    multiRevokeBuiltFree cd + 68 + 32 * arrayCount cd 4 ≤ multiRevokeEncodedEnd cd ∧
      multiRevokeEncodedEnd cd < UInt256.size := by
  have hn := uint64Bound_of_isZero_gt hc.first.length
  change arrayCount cd 4 ≤ solcMaxU64 at hn
  obtain ⟨_, hfree, _⟩ := multiRevokeBuiltMemory_bounds hc hshape hrows
  have hupper := pairRequestsEncodedEnd_upper
    (dst := multiRevokeBuiltFree cd + 4 + 64 + 32 * arrayCount cd 4)
    (counts := multiRevokeCounts cd) (i := 0) (remaining := arrayCount cd 4) (cap := solcMaxU64)
    (by intro j hj hj'
        exact uint64Bound_of_isZero_gt (hrows j (by rw [hshape.2]; omega)).1.length)
  have hlower := pairRequestsEncodedEnd_lower
    (multiRevokeBuiltFree cd + 4 + 64 + 32 * arrayCount cd 4)
    (multiRevokeCounts cd) 0 (arrayCount cd 4)
  change multiRevokeBuiltFree cd + 4 + 64 + 32 * arrayCount cd 4 ≤
    multiRevokeEncodedEnd cd at hlower
  change multiRevokeEncodedEnd cd ≤ _ at hupper
  constructor
  · omega
  · norm_num only [solcMaxU64, UInt256.size] at hn hfree hupper ⊢
    omega

theorem multiRevokeEncodedMemory_size {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    (multiRevokeEncodedMemory cd).size = multiRevokeEncodedEnd cd := by
  have he := (multiRevokeEncodedEnd_bounds hc hshape hrows).1
  rw [multiRevokeEncodedMemory, pairRequestsABIMemory_size, writeWord_sparse_size,
    multiRevokeBuiltMemory_size hshape hrows]
  change max (max (multiRevokeBuiltFree cd) (multiRevokeBuiltFree cd + 32))
    (multiRevokeEncodedEnd cd) = _
  omega

theorem multiRevokeEncodedMemory_freePtr {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    memLoad (UInt256.ofNat 64) (multiRevokeEncodedMemory cd) =
      UInt256.ofNat (multiRevokeBuiltFree cd) := by
  have hf := multiRevokeBuiltMemory_bounds hc hshape hrows
  have he := multiRevokeEncodedEnd_bounds hc hshape hrows
  have hm := multiRevokeBuiltMemory_size hshape hrows
  have hread : (multiRevokeEncodedMemory cd).readWithPadding 64 32 =
      (multiRevokeBuiltMemory cd).readWithPadding 64 32 := by
    rw [multiRevokeEncodedMemory, pairRequestsABIMemory_read_below
      (by rw [writeWord_sparse_size, hm]; omega) (by omega),
      writeWord_sparse_read_preserved_unbounded _ _ _ _ _ (by omega) (.inl (by omega))]
  rw [← multiRevokeBuiltMemory_freePtr (cd := cd)]
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 from rfl,
    if_neg (by rw [multiRevokeEncodedMemory_size hc hshape hrows]; omega),
    if_neg (by omega), hread]

theorem multiRevokeEncodedMemory_read {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    (multiRevokeEncodedMemory cd).readWithPadding (multiRevokeBuiltFree cd)
      (multiRevokeEncodedEnd cd - multiRevokeBuiltFree cd) =
      multiRevokeSelector ++ wordBytes (pairRequestsABIWords (multiRevokeBuiltFree cd + 4)
        (arrayCount cd 4) (multiRevokeSchemas cd) (multiRevokeCounts cd) (multiRevokeValues cd)) :=
            by
  have he := (multiRevokeEncodedEnd_bounds hc hshape hrows).1
  have hlen : multiRevokeEncodedEnd cd - multiRevokeBuiltFree cd =
      4 + 32 * (pairRequestsABIWords (multiRevokeBuiltFree cd + 4) (arrayCount cd 4)
        (multiRevokeSchemas cd) (multiRevokeCounts cd) (multiRevokeValues cd)).length := by
    rw [multiRevokeEncodedEnd, pairRequestsABIEnd,
      pairRequestsEncodedEnd_eq _ (multiRevokeSchemas cd) _ (multiRevokeValues cd),
      pairRequestsABIWords_length]
    omega
  have hsel : (writeWord (multiRevokeBuiltMemory cd) (multiRevokeBuiltFree cd)
      multiRevokeSelectorWord).readWithPadding (multiRevokeBuiltFree cd) 4 =
        multiRevokeSelector := by
    have hr := writeWord_sparse_read_window (multiRevokeBuiltMemory cd)
      (multiRevokeBuiltFree cd) 0 4 multiRevokeSelectorWord (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero, Nat.zero_add, show multiRevokeSelectorWord.toByteArray.extract 0 4 =
      multiRevokeSelector from by native_decide] using hr
  rw [hlen, readWithPadding_split _ _ _ _
    (by rw [multiRevokeEncodedMemory_size hc hshape hrows]; omega),
    multiRevokeEncodedMemory, pairRequestsABIMemory_read,
    pairRequestsABIMemory_read_below (by rw [writeWord_sparse_size]; omega) (by omega), hsel]

theorem multiRevokeRequests_encoding {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    config.externalABI.encode? "multiRevoke" [multiRevokeRequests cd] =
      some ((multiRevokeEncodedMemory cd).readWithPadding (multiRevokeBuiltFree cd)
        (multiRevokeEncodedEnd cd - multiRevokeBuiltFree cd)) := by
  rw [multiRevokeEncodedMemory_read hc hshape hrows]
  change encodeCallWithSelector? multiRevokeSelector
    [.dynamicArray (.tuple [abiBytes32, .dynamicArray (.tuple [abiBytes32, abiUInt256])])]
    [.array (pairRequestsValues (multiRevokeSchemas cd) (multiRevokeCounts cd)
      (multiRevokeValues cd) 0 (arrayCount cd 4))] = _
  rw [encodeCallWithSelector?, pairRequestsValues_encoding _ _ _ (multiRevokeBuiltFree cd + 4)]
  simp only [bind, Option.bind, byteArray_toList_toByteArray]

end Benchmarks.EAS.Attester
