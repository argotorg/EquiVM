import Benchmarks.EAS.Attester.MultiAttestHeap
import Benchmarks.EAS.Attester.AttestRequestsABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def multiAttestSchemas (cd : ByteArray) (i : Nat) : UInt256 :=
  calldataWord cd (arrayDataNat cd 4 + 32 * i)

def multiAttestCounts (cd : ByteArray) (i : Nat) : Nat :=
  (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat

def multiAttestValues (cd : ByteArray) (i j : Nat) : UInt256 :=
  calldataWord cd ((rowData cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 * j)

def multiAttestRequests (cd : ByteArray) : Value :=
  .array (attestRequestsValues (multiAttestSchemas cd) (multiAttestCounts cd)
    (multiAttestValues cd) 0 (arrayCount cd 4))

def multiAttestSelectorWord : UInt256 :=
  UInt256.ofNat 31064325874323733141834184871827779327153766494793685066001561027745075429376

def multiAttestEncodedMemory (cd : ByteArray) : ByteArray :=
  attestRequestsABIMemory (writeWord (multiAttestBuiltMemory cd) (multiAttestBuiltFree cd)
    multiAttestSelectorWord) (multiAttestBuiltFree cd + 4) (arrayCount cd 4)
    (multiAttestSchemas cd) (multiAttestCounts cd) (multiAttestValues cd)

def multiAttestEncodedEnd (cd : ByteArray) : Nat :=
  attestRequestsABIEnd (multiAttestBuiltFree cd + 4) (arrayCount cd 4) (multiAttestCounts cd)

theorem multiAttestEncodedEnd_bounds {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    multiAttestBuiltFree cd + 68 + 32 * arrayCount cd 4 ≤ multiAttestEncodedEnd cd ∧
      multiAttestEncodedEnd cd + 32 < UInt256.size := by
  have hn := uint64Bound_of_isZero_gt hc.first.length
  change arrayCount cd 4 ≤ solcMaxU64 at hn
  obtain ⟨_, hfree, _⟩ := multiAttestBuiltMemory_bounds hc hshape hrows
  have hupper := attestRequestsEncodedEnd_upper
    (dst := multiAttestBuiltFree cd + 4 + 64 + 32 * arrayCount cd 4)
    (counts := multiAttestCounts cd) (i := 0) (remaining := arrayCount cd 4) (cap := solcMaxU64)
    (by intro j hj hj'
        exact uint64Bound_of_isZero_gt (hrows j (by rw [hshape.2]; omega)).1.length)
  have hlower := attestRequestsEncodedEnd_lower
    (multiAttestBuiltFree cd + 4 + 64 + 32 * arrayCount cd 4)
    (multiAttestCounts cd) 0 (arrayCount cd 4)
  change multiAttestBuiltFree cd + 4 + 64 + 32 * arrayCount cd 4 ≤
    multiAttestEncodedEnd cd at hlower
  change multiAttestEncodedEnd cd ≤ _ at hupper
  constructor
  · omega
  · norm_num only [solcMaxU64, UInt256.size] at hn hfree hupper ⊢
    omega

theorem multiAttestEncodedMemory_size {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    (multiAttestEncodedMemory cd).size = multiAttestEncodedEnd cd + 32 := by
  have he := (multiAttestEncodedEnd_bounds hc hshape hrows).1
  rw [multiAttestEncodedMemory, attestRequestsABIMemory_size hshape.1
      (by
        intro j hj
        have hn := (hrows j (by rw [hshape.2]; omega)).2
        exact Nat.pos_of_ne_zero (fun hz ↦ hn (uint256_toNat_eq_zero hz))), writeWord_sparse_size,
    multiAttestBuiltMemory_size hshape hrows]
  change max (max (multiAttestBuiltFree cd) (multiAttestBuiltFree cd + 32))
    (multiAttestEncodedEnd cd + 32) = _
  omega

theorem multiAttestEncodedMemory_freePtr {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    memLoad (UInt256.ofNat 64) (multiAttestEncodedMemory cd) =
      UInt256.ofNat (multiAttestBuiltFree cd) := by
  have hf := multiAttestBuiltMemory_bounds hc hshape hrows
  have he := multiAttestEncodedEnd_bounds hc hshape hrows
  have hm := multiAttestBuiltMemory_size hshape hrows
  have hread : (multiAttestEncodedMemory cd).readWithPadding 64 32 =
      (multiAttestBuiltMemory cd).readWithPadding 64 32 := by
    rw [multiAttestEncodedMemory, attestRequestsABIMemory_read_below
      (by rw [writeWord_sparse_size, hm]; omega) (by omega),
      writeWord_sparse_read_preserved_unbounded _ _ _ _ _ (by omega) (.inl (by omega))]
  rw [← multiAttestBuiltMemory_freePtr (cd := cd)]
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 from rfl,
    if_neg (by rw [multiAttestEncodedMemory_size hc hshape hrows]; omega),
    if_neg (by omega), hread]

theorem multiAttestEncodedMemory_read {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    (multiAttestEncodedMemory cd).readWithPadding (multiAttestBuiltFree cd)
      (multiAttestEncodedEnd cd - multiAttestBuiltFree cd) =
      multiAttestSelector ++ wordBytes (attestRequestsABIWords (multiAttestBuiltFree cd + 4)
        (arrayCount cd 4) (multiAttestSchemas cd) (multiAttestCounts cd) (multiAttestValues cd)) :=
            by
  have he := (multiAttestEncodedEnd_bounds hc hshape hrows).1
  have hlen : multiAttestEncodedEnd cd - multiAttestBuiltFree cd =
      4 + 32 * (attestRequestsABIWords (multiAttestBuiltFree cd + 4) (arrayCount cd 4)
        (multiAttestSchemas cd) (multiAttestCounts cd) (multiAttestValues cd)).length := by
    rw [multiAttestEncodedEnd, attestRequestsABIEnd,
      attestRequestsEncodedEnd_eq _ (multiAttestSchemas cd) _ (multiAttestValues cd),
      attestRequestsABIWords_length]
    omega
  have hsel : (writeWord (multiAttestBuiltMemory cd) (multiAttestBuiltFree cd)
      multiAttestSelectorWord).readWithPadding (multiAttestBuiltFree cd) 4 =
        multiAttestSelector := by
    have hr := writeWord_sparse_read_window (multiAttestBuiltMemory cd)
      (multiAttestBuiltFree cd) 0 4 multiAttestSelectorWord (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero, Nat.zero_add, show multiAttestSelectorWord.toByteArray.extract 0 4 =
      multiAttestSelector from by decide +kernel] using hr
  rw [hlen, readWithPadding_split _ _ _ _
    (by rw [multiAttestEncodedMemory_size hc hshape hrows]; omega),
    multiAttestEncodedMemory, attestRequestsABIMemory_read,
    attestRequestsABIMemory_read_below (by rw [writeWord_sparse_size]; omega) (by omega), hsel]

theorem multiAttestRequests_encoding {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    config.externalABI.encode? "multiAttest" [multiAttestRequests cd] =
      some ((multiAttestEncodedMemory cd).readWithPadding (multiAttestBuiltFree cd)
        (multiAttestEncodedEnd cd - multiAttestBuiltFree cd)) := by
  rw [multiAttestEncodedMemory_read hc hshape hrows]
  change encodeCallWithSelector? multiAttestSelector
    [.dynamicArray (.tuple [bytes32, .dynamicArray (attestationRequestDataTy)])]
    [.array (attestRequestsValues (multiAttestSchemas cd) (multiAttestCounts cd)
      (multiAttestValues cd) 0 (arrayCount cd 4))] = _
  rw [encodeCallWithSelector?, attestRequestsValues_encoding _ _ _ (multiAttestBuiltFree cd + 4)]
  simp only [bind, Option.bind, byteArray_toList_toByteArray]

end Benchmarks.EAS.Attester
