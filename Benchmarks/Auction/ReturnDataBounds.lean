import Benchmarks.Auction.ReturnDataProperties

open Ethereum Ethereum.EVM

namespace Auction.ReturnDataProperties

-- LIBRARY CANDIDATE: an out-of-bounds precompile input slice is zero.
theorem nat_of_slice_eq_zero {data : ByteArray} {off len : Nat}
    (hoff : data.size ≤ off) : nat_of_slice data off len = 0 := by
  simp [nat_of_slice, ByteArray.readWithoutPadding, hoff, fromByteArrayBigEndian,
    fromBytesBigEndian, fromBytes']

-- GENERALIZES the gas-derived return-data bound for the short call payloads
-- used by Auction. EXPMOD cannot read a nonzero modulus from a 96-byte header.
theorem expmod_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} (hdata : I.calldata.size ≤ 96) :
    (Ξ_EXPMOD σ g A I).2.2.2.size < 2 ^ 64 := by
  have hmod : nat_of_slice I.calldata
      (96 + nat_of_slice I.calldata 0 32 + nat_of_slice I.calldata 32 32)
      (nat_of_slice I.calldata 64 32) = 0 := nat_of_slice_eq_zero (by omega)
  unfold Ξ_EXPMOD
  dsimp only
  simp only [hmod, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  generalize max 200 _ = cost
  split
  · simp
  · simp only [ByteArray_zeroes_size]
    exact USize.toNat_lt _

theorem ecrec_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_ECREC σ g A I).2.2.2.size < 2 ^ 64 := by
  have h12 : (OfNat.ofNat 12 : USize).toNat = 12 := by
    apply USize.toNat_ofNat_of_le_of_lt (n := 12) (i := 12)
    · have := USize.le_size
      omega
    · rfl
  unfold Ξ_ECREC
  by_cases hgas : g.toNat < 3000
  · simp [hgas]
  · simp only [hgas, ↓reduceIte]
    split
    · simp
    · split
      · simp [ByteArray.size_append, ByteArray_zeroes_size, ByteArray.size_extract, h12]
        omega
      · simp [dbgTrace]

theorem sha256_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_SHA256 σ g A I).2.2.2.size < 2 ^ 64 := by
  unfold Ξ_SHA256 ffi.SHA256
  simp [pure, Except.pure]
  split <;> simp [ffi_sha256_output_size]

theorem rip160_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_RIP160 σ g A I).2.2.2.size < 2 ^ 64 := by
  by_cases hgas : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp [Ξ_RIP160, hgas]
  · simp only [Ξ_RIP160, hgas, ↓reduceIte]
    cases hres : RIP160 I.calldata with
    | ok s => simp [RIP160_ok_output_size hres]
    | error e => simp [dbgTrace]

theorem id_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} (hdata : I.calldata.size < 2 ^ 64) :
    (Ξ_ID σ g A I).2.2.2.size < 2 ^ 64 := by
  unfold Ξ_ID
  dsimp only
  split <;> simp_all

theorem bn_add_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_BN_ADD σ g A I).2.2.2.size < 2 ^ 64 := by
  by_cases hgas : g.toNat < 150
  · simp [Ξ_BN_ADD, hgas]
  · simp only [Ξ_BN_ADD, hgas, ↓reduceIte]
    cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) with
    | ok s => simp [BN_ADD_ok_output_size hres]
    | error e => simp [dbgTrace]

theorem bn_mul_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_BN_MUL σ g A I).2.2.2.size < 2 ^ 64 := by
  by_cases hgas : g.toNat < 6000
  · simp [Ξ_BN_MUL, hgas]
  · simp only [Ξ_BN_MUL, hgas, ↓reduceIte]
    cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) with
    | ok s => simp [BN_MUL_ok_output_size hres]
    | error e => simp [dbgTrace]

theorem snarkv_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_SNARKV σ g A I).2.2.2.size < 2 ^ 64 := by
  by_cases hgas : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp [Ξ_SNARKV, hgas]
  · simp only [Ξ_SNARKV, hgas, ↓reduceIte]
    cases hres : SNARKV I.calldata with
    | ok s => simp [SNARKV_ok_output_size hres]
    | error e => simp [dbgTrace]

theorem blake2_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_BLAKE2_F σ g A I).2.2.2.size < 2 ^ 64 := by
  by_cases hgas : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simp [Ξ_BLAKE2_F, hgas, dbgTrace]
  · simp only [Ξ_BLAKE2_F, hgas, ↓reduceIte]
    cases hres : ffi.BLAKE2 I.calldata with
    | ok s => simp [ffi_BLAKE2_ok_output_size hres]
    | error e => simp [dbgTrace]

theorem pointEval_size_lt_2pow64 {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} : (Ξ_PointEval σ g A I).2.2.2.size < 2 ^ 64 := by
  by_cases hgas : g.toNat < 50000
  · simp [Ξ_PointEval, hgas]
  · simp only [Ξ_PointEval, hgas, ↓reduceIte]
    cases hres : PointEval I.calldata with
    | ok s => simp [PointEval_ok_output_size hres]
    | error e => simp [dbgTrace]

set_option maxRecDepth 4096 in
theorem precompile_dispatch_size_lt_2pow64
    (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) (hdata : I.calldata.size ≤ 96) :
    (match pc with
      | 1 => (∅, Ξ_ECREC σ g A I)
      | 2 => (∅, Ξ_SHA256 σ g A I)
      | 3 => (∅, Ξ_RIP160 σ g A I)
      | 4 => (∅, Ξ_ID σ g A I)
      | 5 => (∅, Ξ_EXPMOD σ g A I)
      | 6 => (∅, Ξ_BN_ADD σ g A I)
      | 7 => (∅, Ξ_BN_MUL σ g A I)
      | 8 => (∅, Ξ_SNARKV σ g A I)
      | 9 => (∅, Ξ_BLAKE2_F σ g A I)
      | 10 => (∅, Ξ_PointEval σ g A I)
      | _ => (default : Batteries.RBSet AccountAddress compare ×
          AccountMap × UInt256 × Substate × ByteArray)).2.2.2.2.size < 2 ^ 64 := by
  split
  · exact ecrec_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact sha256_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact rip160_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact id_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I) (by omega)
  · exact expmod_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I) hdata
  · exact bn_add_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact bn_mul_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact snarkv_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact blake2_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact pointEval_size_lt_2pow64 (σ := σ) (g := g) (A := A) (I := I)
  · exact (show (default : ByteArray).size < 2 ^ 64 by decide)

theorem theta_precompiled_size_lt_2pow64
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r pc : AccountAddress) (d : ByteArray) (g p v v' : UInt256)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) (hdata : d.size ≤ 96) :
    (Θ blob cA gh bl σ σ₀ A s o r (.Precompiled pc) g p v v' d e H w).2.2.2.2.2.size <
      2 ^ 64 := by
  unfold Θ
  simp only
  exact precompile_dispatch_size_lt_2pow64 _ _ _ _ _ hdata

theorem theta_size_lt_2pow64
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (code : ToExecute) (d : ByteArray) (g p v v' : UInt256)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) (hdata : d.size ≤ 96) :
    (Θ blob cA gh bl σ σ₀ A s o r code g p v v' d e H w).2.2.2.2.2.size < 2 ^ 64 := by
  cases code with
  | Code code =>
      exact theta_code_size_lt_2pow64 blob cA gh bl σ σ₀ A s o r code d g p v v' e H w
  | Precompiled pc =>
      exact theta_precompiled_size_lt_2pow64 blob cA gh bl σ σ₀ A s o r pc d g p v v'
        e H w hdata

end Auction.ReturnDataProperties
