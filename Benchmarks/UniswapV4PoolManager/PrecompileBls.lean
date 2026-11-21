import Benchmarks.UniswapV4PoolManager.MemoryGas

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 20000

-- BLS field encodings require sixteen leading zero bytes. A large first word violates this.
private theorem blsInputPrefixNonzero {data : ByteArray} (hs : 32 ≤ data.size)
    (hb : 2 ^ 132 ≤ nat_of_slice data 0 32) :
    (data.extract 0 16).data.all (· == 0) = false := by
  by_contra hn
  have hz : data.extract 0 16 = ByteArray.zeroes 16 := by
    apply ByteArray.ext
    unfold ByteArray.zeroes
    change (data.extract 0 16).data = Array.replicate 16 0
    apply Array.eq_replicate_iff.mpr
    constructor
    · have hd : data.data.size = data.size := rfl
      simp only [ByteArray.data_extract, Array.size_extract, hd]
      omega
    · simpa only [Array.all_eq_true', beq_iff_eq] using Bool.eq_true_of_not_eq_false hn
  have hread : nat_of_slice data 0 32 = fromByteArrayBigEndian (data.extract 0 32) := by
    simp [nat_of_slice, readWithoutPadding_eq_extract_total, ByteArray.size_extract,
      Nat.min_eq_left hs]
  rw [hread, ByteArray.extract_eq_extract_append_extract 16 (by omega) (by omega), hz,
    fromByteArrayBigEndian_append,
    show fromByteArrayBigEndian (ByteArray.zeroes 16) = 0 from by decide +kernel,
    Nat.zero_mul, Nat.zero_add] at hb
  have hlt := fromByteArrayBigEndian_lt (data.extract 16 32)
  simp only [ByteArray.size_extract, Nat.min_eq_left hs] at hlt
  norm_num at hlt
  omega

private theorem decodeFpPrefixNone {data : ByteArray} {n : Nat} (hn : 16 ≤ n)
    (hp : (data.extract 0 16).data.all (· == 0) = false) :
    Crypto.BLS12_381.decodeFp (data.extract 0 n) = none := by
  unfold Crypto.BLS12_381.decodeFp
  rw [ByteArray.extract_extract]
  simp only [Nat.zero_add, Nat.min_eq_left hn, hp, Bool.and_false]
  simp

private theorem decodeG1PrefixNone {data : ByteArray}
    (hp : (data.extract 0 16).data.all (· == 0) = false) (subgroup : Bool) :
    Crypto.BLS12_381.decodeG1 (data.extract 0 128) subgroup = none := by
  unfold Crypto.BLS12_381.decodeG1
  rw [ByteArray.extract_extract, Nat.zero_add, Nat.zero_add,
    Nat.min_eq_left (by decide : 64 ≤ 128), decodeFpPrefixNone (by decide) hp]
  cases (guard ((data.extract 0 128).size == 128) : Option Unit) <;> rfl

private theorem decodeG2PrefixNone {data : ByteArray}
    (hp : (data.extract 0 16).data.all (· == 0) = false) (subgroup : Bool) :
    Crypto.BLS12_381.decodeG2 (data.extract 0 256) subgroup = none := by
  unfold Crypto.BLS12_381.decodeG2
  rw [ByteArray.extract_extract, Nat.zero_add, Nat.zero_add,
    Nat.min_eq_left (by decide : 64 ≤ 256), decodeFpPrefixNone (by decide) hp]
  cases (guard ((data.extract 0 256).size == 256) : Option Unit) <;> rfl

private theorem mapChunksNone {α : Type} (f : ByteArray → Option α) {data : ByteArray}
    {size : Nat} (hpos : 0 < data.size / size) (hf : f (data.extract 0 size) = none) :
    ((List.range (data.size / size)).map
      (fun i ↦ data.extract (i * size) ((i + 1) * size))).mapM f = none := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hn, List.range_succ_eq_map, List.map_cons, List.mapM_cons]
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, hf, bind, Option.bind_none]

private theorem blsPrecompileBadPrefix (op : Nat) {data : ByteArray}
    (hp : (data.extract 0 16).data.all (· == 0) = false) :
    Crypto.BLS12_381.precompile op data = none := by
  unfold Crypto.BLS12_381.precompile
  split
  · rw [decodeG1PrefixNone hp]
    cases (guard (data.size == 256) : Option Unit) <;> rfl
  · by_cases hs : (data.size != 0 && data.size % 160 == 0) = true
    · have hpos : 0 < data.size / 160 := by
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hs
        omega
      have hf : (do
          let P ← Crypto.BLS12_381.decodeG1 ((data.extract 0 160).extract 0 128) true
          pure (Crypto.BLS12_381.g1Curve.mul P
            (Crypto.ofBytesBE ((data.extract 0 160).extract 128 160)))) = none := by
        simp only [ByteArray.extract_extract, Nat.zero_add,
          Nat.min_eq_left (by decide : 128 ≤ 160), decodeG1PrefixNone hp, bind,
          Option.bind_none]
      change (Crypto.BLS12_381.encodeG1 <$> do
        guard (data.size != 0 && data.size % 160 == 0)
        let terms ← ((List.range (data.size / 160)).map
          (fun i ↦ data.extract (i * 160) ((i + 1) * 160))).mapM (fun c ↦ do
            let P ← Crypto.BLS12_381.decodeG1 (c.extract 0 128) true
            pure (Crypto.BLS12_381.g1Curve.mul P (Crypto.ofBytesBE (c.extract 128 160))))
        pure (terms.foldl Crypto.BLS12_381.g1Curve.add Crypto.Jac.infinity)) = none
      rw [mapChunksNone (fun c ↦ do
        let P ← Crypto.BLS12_381.decodeG1 (c.extract 0 128) true
        pure (Crypto.BLS12_381.g1Curve.mul P (Crypto.ofBytesBE (c.extract 128 160)))) hpos hf]
      cases (guard (data.size != 0 && data.size % 160 == 0) : Option Unit) <;> rfl
    · simp [hs]
  · rw [decodeG2PrefixNone hp]
    cases (guard (data.size == 512) : Option Unit) <;> rfl
  · by_cases hs : (data.size != 0 && data.size % 288 == 0) = true
    · have hpos : 0 < data.size / 288 := by
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hs
        omega
      have hf : (do
          let Q ← Crypto.BLS12_381.decodeG2 ((data.extract 0 288).extract 0 256) true
          pure (Crypto.BLS12_381.g2Curve.mul Q
            (Crypto.ofBytesBE ((data.extract 0 288).extract 256 288)))) = none := by
        simp only [ByteArray.extract_extract, Nat.zero_add,
          Nat.min_eq_left (by decide : 256 ≤ 288), decodeG2PrefixNone hp, bind,
          Option.bind_none]
      change (Crypto.BLS12_381.encodeG2 <$> do
        guard (data.size != 0 && data.size % 288 == 0)
        let terms ← ((List.range (data.size / 288)).map
          (fun i ↦ data.extract (i * 288) ((i + 1) * 288))).mapM (fun c ↦ do
            let P ← Crypto.BLS12_381.decodeG2 (c.extract 0 256) true
            pure (Crypto.BLS12_381.g2Curve.mul P (Crypto.ofBytesBE (c.extract 256 288))))
        pure (terms.foldl Crypto.BLS12_381.g2Curve.add Crypto.Jac.infinity)) = none
      rw [mapChunksNone (fun c ↦ do
        let P ← Crypto.BLS12_381.decodeG2 (c.extract 0 256) true
        pure (Crypto.BLS12_381.g2Curve.mul P (Crypto.ofBytesBE (c.extract 256 288)))) hpos hf]
      cases (guard (data.size != 0 && data.size % 288 == 0) : Option Unit) <;> rfl
    · simp [hs]
  · by_cases hs : (data.size != 0 && data.size % 384 == 0) = true
    · have hpos : 0 < data.size / 384 := by
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hs
        omega
      have hf : (do
          let P ← Crypto.BLS12_381.decodeG1 ((data.extract 0 384).extract 0 128) true
          let Q ← Crypto.BLS12_381.decodeG2 ((data.extract 0 384).extract 128 384) true
          pure (P, Q)) = none := by
        simp only [ByteArray.extract_extract, Nat.zero_add,
          Nat.min_eq_left (by decide : 128 ≤ 384), decodeG1PrefixNone hp, bind,
          Option.bind_none]
      change ((fun ok ↦ Crypto.toBytesBE (if ok then 1 else 0) 32) <$> do
        guard (data.size != 0 && data.size % 384 == 0)
        let pairs ← ((List.range (data.size / 384)).map
          (fun i ↦ data.extract (i * 384) ((i + 1) * 384))).mapM (fun c ↦ do
            let P ← Crypto.BLS12_381.decodeG1 (c.extract 0 128) true
            let Q ← Crypto.BLS12_381.decodeG2 (c.extract 128 384) true
            pure (P, Q))
        pure (Crypto.BLS12_381.pairingCheck pairs)) = none
      rw [mapChunksNone (fun c ↦ do
        let P ← Crypto.BLS12_381.decodeG1 (c.extract 0 128) true
        let Q ← Crypto.BLS12_381.decodeG2 (c.extract 128 384) true
        pure (P, Q)) hpos hf]
      cases (guard (data.size != 0 && data.size % 384 == 0) : Option Unit) <;> rfl
    · simp [hs]
  · have hfp : Crypto.BLS12_381.decodeFp data = none := by
      unfold Crypto.BLS12_381.decodeFp
      rw [hp]
      simp
    rw [hfp]
    cases (guard (data.size == 64) : Option Unit) <;> rfl
  · rw [decodeFpPrefixNone (by decide) hp]
    cases (guard (data.size == 128) : Option Unit) <;> rfl
  · rfl

theorem precompile_BLS12_381_large_first_word (op : Nat)
    {σ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hb : 2 ^ 132 ≤ nat_of_slice I.calldata 0 32) :
    Ξ_BLS12_381 op σ g A I = (∅, ⟨0⟩, A, .empty) := by
  have hbls : ∃ err, BLS12_381 op I.calldata = .error err := by
    unfold BLS12_381
    by_cases hv : blsInputLengthValid op I.calldata.size = true
    · have hs : 32 ≤ I.calldata.size := by
        unfold blsInputLengthValid at hv
        split at hv <;>
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Bool.false_eq_true] at hv <;>
          omega
      rw [hv]
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [blsPrecompileBadPrefix op (blsInputPrefixNonzero hs hb)]
      exact ⟨_, rfl⟩
    · simp [Bool.eq_false_of_not_eq_true hv]
  obtain ⟨err, herr⟩ := hbls
  simp [Ξ_BLS12_381, herr]

end Benchmarks.UniswapV4PoolManager
