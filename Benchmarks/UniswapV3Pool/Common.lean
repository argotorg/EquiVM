import Benchmarks.UniswapV3Pool.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.JumpDest
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Refinement
import Reasoning.Solc
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# UniswapV3Pool shared proof facts

Contract-wide selector, dispatch, and revert facts used by the top-level runtime proof and the
per-function body proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.UniswapV3Pool.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.UniswapV3Pool

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev uniswapV3PoolSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- UniswapV3Pool selectors in increasing selector order, matching the deployed dispatcher tree. -/
def uniswapV3PoolSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩ -- token0()
  | 1 => ⟨#[0x12, 0x8a, 0xcb, 0x08]⟩ -- swap(address,bool,int256,uint160,bytes)
  | 2 => ⟨#[0x1a, 0x68, 0x65, 0x02]⟩ -- liquidity()
  | 3 => ⟨#[0x1a, 0xd8, 0xb0, 0x3b]⟩ -- protocolFees()
  | 4 => ⟨#[0x25, 0x2c, 0x09, 0xd7]⟩ -- observations(uint256)
  | 5 => ⟨#[0x32, 0x14, 0x8f, 0x67]⟩ -- increaseObservationCardinalityNext(uint16)
  | 6 => ⟨#[0x38, 0x50, 0xc7, 0xbd]⟩ -- slot0()
  | 7 => ⟨#[0x3c, 0x8a, 0x7d, 0x8d]⟩ -- mint(address,int24,int24,uint128,bytes)
  | 8 => ⟨#[0x46, 0x14, 0x13, 0x19]⟩ -- feeGrowthGlobal1X128()
  | 9 => ⟨#[0x49, 0x0e, 0x6c, 0xbc]⟩ -- flash(address,uint256,uint256,bytes)
  | 10 => ⟨#[0x4f, 0x1e, 0xb3, 0xd8]⟩ -- collect(address,int24,int24,uint128,uint128)
  | 11 => ⟨#[0x51, 0x4e, 0xa4, 0xbf]⟩ -- positions(bytes32)
  | 12 => ⟨#[0x53, 0x39, 0xc2, 0x96]⟩ -- tickBitmap(int16)
  | 13 => ⟨#[0x70, 0xcf, 0x75, 0x4a]⟩ -- maxLiquidityPerTick()
  | 14 => ⟨#[0x82, 0x06, 0xa4, 0xd1]⟩ -- setFeeProtocol(uint8,uint8)
  | 15 => ⟨#[0x85, 0xb6, 0x67, 0x29]⟩ -- collectProtocol(address,uint128,uint128)
  | 16 => ⟨#[0x88, 0x3b, 0xdb, 0xfd]⟩ -- observe(uint32[])
  | 17 => ⟨#[0xa3, 0x41, 0x23, 0xa7]⟩ -- burn(int24,int24,uint128)
  | 18 => ⟨#[0xa3, 0x88, 0x07, 0xf2]⟩ -- snapshotCumulativesInside(int24,int24)
  | 19 => ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩ -- factory()
  | 20 => ⟨#[0xd0, 0xc9, 0x3a, 0x7c]⟩ -- tickSpacing()
  | 21 => ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩ -- token1()
  | 22 => ⟨#[0xdd, 0xca, 0x3f, 0x43]⟩ -- fee()
  | 23 => ⟨#[0xf3, 0x05, 0x83, 0x99]⟩ -- feeGrowthGlobal0X128()
  | 24 => ⟨#[0xf3, 0x0d, 0xba, 0x93]⟩ -- ticks(int24)
  | _ => ⟨#[0xf6, 0x37, 0x73, 0x1d]⟩ -- initialize(uint160)

/-- Numeric selector words in the same order as `uniswapV3PoolSelBytes`. -/
def uniswapV3PoolSelNat : ℕ → UInt256
  | 0 => ⟨234755713⟩
  | 1 => ⟨311085832⟩
  | 2 => ⟨443049218⟩
  | 3 => ⟨450408507⟩
  | 4 => ⟨623643095⟩
  | 5 => ⟨840208231⟩
  | 6 => ⟨944818109⟩
  | 7 => ⟨1015709069⟩
  | 8 => ⟨1175720729⟩
  | 9 => ⟨1225682108⟩
  | 10 => ⟨1327412184⟩
  | 11 => ⟨1364108479⟩
  | 12 => ⟨1396294294⟩
  | 13 => ⟨1892644170⟩
  | 14 => ⟨2181473489⟩
  | 15 => ⟨2243323689⟩
  | 16 => ⟨2285624317⟩
  | 17 => ⟨2738955175⟩
  | 18 => ⟨2743601138⟩
  | 19 => ⟨3294232917⟩
  | 20 => ⟨3502848636⟩
  | 21 => ⟨3524403367⟩
  | 22 => ⟨3721019203⟩
  | 23 => ⟨4077224857⟩
  | 24 => ⟨4077763219⟩
  | _ => ⟨4130829085⟩

/-- EVM selector-word comparison agrees with comparing the calldata's first four bytes. -/
theorem uniswapV3PoolSelectorEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (i : ℕ) (hi : i < 26) :
    UInt256.eq (uniswapV3PoolSelNat i) (uniswapV3PoolSelWord I) =
      if (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases i <;>
    exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem uniswapV3PoolSelectorEq_zero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (i : ℕ) (hi : i < 26) :
    UInt256.eq (uniswapV3PoolSelNat i) (uniswapV3PoolSelWord I) = ⟨0⟩ := by
  rw [uniswapV3PoolSelectorEq I hsz i hi, hnm i hi]
  rfl

theorem byteArray_beq_false_of_ne_of_beq_true {a b x : ByteArray}
    (hne : a ≠ b) (hbx : (b == x) = true) :
    (a == x) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hax
  have hax' : a = x := by
    apply ByteArray.ext
    exact LawfulBEq.eq_of_beq (show (a.data == x.data) = true from hax)
  have hbx' : b = x := by
    apply ByteArray.ext
    exact LawfulBEq.eq_of_beq (show (b.data == x.data) = true from hbx)
  apply hne
  exact hax'.trans hbx'.symm

theorem uniswapV3PoolSelectorMissOfHit (I : ExecutionEnv) {i j : ℕ}
    (hne : uniswapV3PoolSelBytes i ≠ uniswapV3PoolSelBytes j)
    (hhit : (uniswapV3PoolSelBytes j == I.calldata.extract 0 4) = true) :
    (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false :=
  byteArray_beq_false_of_ne_of_beq_true hne hhit

theorem uniswapV3PoolSelectorMissOfHitBytes {cd : ByteArray} {i j : ℕ}
    (hne : uniswapV3PoolSelBytes i ≠ uniswapV3PoolSelBytes j)
    (hhit : (uniswapV3PoolSelBytes j == cd.extract 0 4) = true) :
    (uniswapV3PoolSelBytes i == cd.extract 0 4) = false :=
  byteArray_beq_false_of_ne_of_beq_true hne hhit

theorem uniswapV3PoolSelectorMatchCases (I : ExecutionEnv)
    (hnot : ¬ ∀ i, i < 26 →
      (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    {P : Prop}
    (h0 : (uniswapV3PoolSelBytes 0 == I.calldata.extract 0 4) = true → P)
    (h1 : (uniswapV3PoolSelBytes 1 == I.calldata.extract 0 4) = true → P)
    (h2 : (uniswapV3PoolSelBytes 2 == I.calldata.extract 0 4) = true → P)
    (h3 : (uniswapV3PoolSelBytes 3 == I.calldata.extract 0 4) = true → P)
    (h4 : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true → P)
    (h5 : (uniswapV3PoolSelBytes 5 == I.calldata.extract 0 4) = true → P)
    (h6 : (uniswapV3PoolSelBytes 6 == I.calldata.extract 0 4) = true → P)
    (h7 : (uniswapV3PoolSelBytes 7 == I.calldata.extract 0 4) = true → P)
    (h8 : (uniswapV3PoolSelBytes 8 == I.calldata.extract 0 4) = true → P)
    (h9 : (uniswapV3PoolSelBytes 9 == I.calldata.extract 0 4) = true → P)
    (h10 : (uniswapV3PoolSelBytes 10 == I.calldata.extract 0 4) = true → P)
    (h11 : (uniswapV3PoolSelBytes 11 == I.calldata.extract 0 4) = true → P)
    (h12 : (uniswapV3PoolSelBytes 12 == I.calldata.extract 0 4) = true → P)
    (h13 : (uniswapV3PoolSelBytes 13 == I.calldata.extract 0 4) = true → P)
    (h14 : (uniswapV3PoolSelBytes 14 == I.calldata.extract 0 4) = true → P)
    (h15 : (uniswapV3PoolSelBytes 15 == I.calldata.extract 0 4) = true → P)
    (h16 : (uniswapV3PoolSelBytes 16 == I.calldata.extract 0 4) = true → P)
    (h17 : (uniswapV3PoolSelBytes 17 == I.calldata.extract 0 4) = true → P)
    (h18 : (uniswapV3PoolSelBytes 18 == I.calldata.extract 0 4) = true → P)
    (h19 : (uniswapV3PoolSelBytes 19 == I.calldata.extract 0 4) = true → P)
    (h20 : (uniswapV3PoolSelBytes 20 == I.calldata.extract 0 4) = true → P)
    (h21 : (uniswapV3PoolSelBytes 21 == I.calldata.extract 0 4) = true → P)
    (h22 : (uniswapV3PoolSelBytes 22 == I.calldata.extract 0 4) = true → P)
    (h23 : (uniswapV3PoolSelBytes 23 == I.calldata.extract 0 4) = true → P)
    (h24 : (uniswapV3PoolSelBytes 24 == I.calldata.extract 0 4) = true → P)
    (h25 : (uniswapV3PoolSelBytes 25 == I.calldata.extract 0 4) = true → P) :
    P := by
  by_cases h0m : (uniswapV3PoolSelBytes 0 == I.calldata.extract 0 4) = true
  · exact h0 h0m
  by_cases h1m : (uniswapV3PoolSelBytes 1 == I.calldata.extract 0 4) = true
  · exact h1 h1m
  by_cases h2m : (uniswapV3PoolSelBytes 2 == I.calldata.extract 0 4) = true
  · exact h2 h2m
  by_cases h3m : (uniswapV3PoolSelBytes 3 == I.calldata.extract 0 4) = true
  · exact h3 h3m
  by_cases h4m : (uniswapV3PoolSelBytes 4 == I.calldata.extract 0 4) = true
  · exact h4 h4m
  by_cases h5m : (uniswapV3PoolSelBytes 5 == I.calldata.extract 0 4) = true
  · exact h5 h5m
  by_cases h6m : (uniswapV3PoolSelBytes 6 == I.calldata.extract 0 4) = true
  · exact h6 h6m
  by_cases h7m : (uniswapV3PoolSelBytes 7 == I.calldata.extract 0 4) = true
  · exact h7 h7m
  by_cases h8m : (uniswapV3PoolSelBytes 8 == I.calldata.extract 0 4) = true
  · exact h8 h8m
  by_cases h9m : (uniswapV3PoolSelBytes 9 == I.calldata.extract 0 4) = true
  · exact h9 h9m
  by_cases h10m : (uniswapV3PoolSelBytes 10 == I.calldata.extract 0 4) = true
  · exact h10 h10m
  by_cases h11m : (uniswapV3PoolSelBytes 11 == I.calldata.extract 0 4) = true
  · exact h11 h11m
  by_cases h12m : (uniswapV3PoolSelBytes 12 == I.calldata.extract 0 4) = true
  · exact h12 h12m
  by_cases h13m : (uniswapV3PoolSelBytes 13 == I.calldata.extract 0 4) = true
  · exact h13 h13m
  by_cases h14m : (uniswapV3PoolSelBytes 14 == I.calldata.extract 0 4) = true
  · exact h14 h14m
  by_cases h15m : (uniswapV3PoolSelBytes 15 == I.calldata.extract 0 4) = true
  · exact h15 h15m
  by_cases h16m : (uniswapV3PoolSelBytes 16 == I.calldata.extract 0 4) = true
  · exact h16 h16m
  by_cases h17m : (uniswapV3PoolSelBytes 17 == I.calldata.extract 0 4) = true
  · exact h17 h17m
  by_cases h18m : (uniswapV3PoolSelBytes 18 == I.calldata.extract 0 4) = true
  · exact h18 h18m
  by_cases h19m : (uniswapV3PoolSelBytes 19 == I.calldata.extract 0 4) = true
  · exact h19 h19m
  by_cases h20m : (uniswapV3PoolSelBytes 20 == I.calldata.extract 0 4) = true
  · exact h20 h20m
  by_cases h21m : (uniswapV3PoolSelBytes 21 == I.calldata.extract 0 4) = true
  · exact h21 h21m
  by_cases h22m : (uniswapV3PoolSelBytes 22 == I.calldata.extract 0 4) = true
  · exact h22 h22m
  by_cases h23m : (uniswapV3PoolSelBytes 23 == I.calldata.extract 0 4) = true
  · exact h23 h23m
  by_cases h24m : (uniswapV3PoolSelBytes 24 == I.calldata.extract 0 4) = true
  · exact h24 h24m
  by_cases h25m : (uniswapV3PoolSelBytes 25 == I.calldata.extract 0 4) = true
  · exact h25 h25m
  exfalso
  apply hnot
  intro i hi
  interval_cases i
  · exact Bool.eq_false_of_not_eq_true h0m
  · exact Bool.eq_false_of_not_eq_true h1m
  · exact Bool.eq_false_of_not_eq_true h2m
  · exact Bool.eq_false_of_not_eq_true h3m
  · exact Bool.eq_false_of_not_eq_true h4m
  · exact Bool.eq_false_of_not_eq_true h5m
  · exact Bool.eq_false_of_not_eq_true h6m
  · exact Bool.eq_false_of_not_eq_true h7m
  · exact Bool.eq_false_of_not_eq_true h8m
  · exact Bool.eq_false_of_not_eq_true h9m
  · exact Bool.eq_false_of_not_eq_true h10m
  · exact Bool.eq_false_of_not_eq_true h11m
  · exact Bool.eq_false_of_not_eq_true h12m
  · exact Bool.eq_false_of_not_eq_true h13m
  · exact Bool.eq_false_of_not_eq_true h14m
  · exact Bool.eq_false_of_not_eq_true h15m
  · exact Bool.eq_false_of_not_eq_true h16m
  · exact Bool.eq_false_of_not_eq_true h17m
  · exact Bool.eq_false_of_not_eq_true h18m
  · exact Bool.eq_false_of_not_eq_true h19m
  · exact Bool.eq_false_of_not_eq_true h20m
  · exact Bool.eq_false_of_not_eq_true h21m
  · exact Bool.eq_false_of_not_eq_true h22m
  · exact Bool.eq_false_of_not_eq_true h23m
  · exact Bool.eq_false_of_not_eq_true h24m
  · exact Bool.eq_false_of_not_eq_true h25m

private theorem byteArray_prefix_suffix (b : ByteArray) (n : Nat) (hn : n ≤ b.size) :
    b.extract 0 n ++ b.extract n b.size = b := by
  rw [ByteArray.extract_append_extract]
  rw [show min 0 n = 0 by omega, show max n b.size = b.size by omega]
  exact byteArray_extract_self b

private theorem spliceBytes?_eq_pref_append {pref rest value out : ByteArray} {offset : Nat}
    (h : spliceBytes? (pref ++ rest) offset value = some out) (hoff : pref.size ≤ offset) :
    ∃ rest', out = pref ++ rest' := by
  unfold spliceBytes? at h
  split at h
  · cases h
    refine ⟨rest.extract 0 (offset - pref.size) ++ value ++
      (pref ++ rest).extract (offset + value.size) (pref ++ rest).size, ?_⟩
    rw [extract_append_span]
    · rw [byteArray_extract_self]
      simp only [ByteArray.append_assoc]
    · omega
    · omega
  · simp at h

private theorem patchRuntime_eq_pref_append_aux (ps : List (Nat × ByteArray))
    {pref acc out : ByteArray} (hacc : ∃ rest, acc = pref ++ rest)
    (hall : ∀ p ∈ ps, pref.size ≤ p.1)
    (h : ps.foldlM (fun acc p =>
      if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none) acc = some out) :
    ∃ rest, out = pref ++ rest := by
  induction ps generalizing acc with
  | nil =>
      simp at h
      cases h
      exact hacc
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at h
        rcases hacc with ⟨rest, rfl⟩
        cases hsp : spliceBytes? (pref ++ rest) p.1 p.2 with
        | none => simp [hsp] at h
        | some acc' =>
            simp [hsp] at h
            exact ih (hacc := spliceBytes?_eq_pref_append hsp (hall p (by simp)))
              (hall := fun q hq => hall q (by simp [hq])) h
      · rw [if_neg hsz] at h
        simp at h

private theorem patchRuntime_eq_pref_append {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {n : Nat} (hn : n ≤ template.size)
    (hall : ∀ p ∈ ps, n ≤ p.1) (h : patchRuntime template ps = some out) :
    ∃ rest, out = template.extract 0 n ++ rest := by
  unfold patchRuntime at h
  refine patchRuntime_eq_pref_append_aux ps ?_ ?_ h
  · exact ⟨template.extract n template.size, (byteArray_prefix_suffix template n hn).symm⟩
  · intro p hp
    simpa [ByteArray.size_extract, hn] using hall p hp

private theorem uniswapV3Pool_patches_ge_2258 (v : PoolImmutables) :
    ∀ p ∈ patches v, 2258 ≤ p.1 := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

/-- Patching immutables preserves the runtime prefix before the first immutable reference. -/
theorem uniswapV3PoolPatchedPrefix2258 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    ∃ rest, code = uniswapV3PoolBytecode.extract 0 2258 ++ rest := by
  exact patchRuntime_eq_pref_append (by native_decide) (uniswapV3Pool_patches_ge_2258 v) hpatch

/-- Any instruction whose maximal decode window is before the first immutable patch is unchanged. -/
theorem uniswapV3PoolDecodePatchedEqTemplate2258 {v : PoolImmutables} {code : ByteArray}
    {pc : UInt256} (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 33 ≤ 2258) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  let pref := uniswapV3PoolBytecode.extract 0 2258
  let tail0 := uniswapV3PoolBytecode.extract 2258 uniswapV3PoolBytecode.size
  obtain ⟨tail, htail⟩ := uniswapV3PoolPatchedPrefix2258 hpatch
  have htemplate : uniswapV3PoolBytecode = pref ++ tail0 := by
    dsimp [pref, tail0]
    exact (byteArray_prefix_suffix uniswapV3PoolBytecode 2258 (by native_decide)).symm
  have hprefSize : pref.size = 2258 := by
    dsimp [pref]
    rw [ByteArray.size_extract]
    have hs : 2258 ≤ uniswapV3PoolBytecode.size := by native_decide
    omega
  rw [htail]
  change decode (pref ++ tail) pc = decode uniswapV3PoolBytecode pc
  rw [decode_append_left_window pref tail pc (by rw [hprefSize]; exact hwin)
    (by rw [hprefSize]; norm_num)]
  rw [htemplate]
  rw [decode_append_left_window pref tail0 pc (by rw [hprefSize]; exact hwin)
    (by rw [hprefSize]; norm_num)]

private theorem spliceBytes?_extract_before {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hbefore : stop ≤ offset) :
    out.extract start stop = b.extract start stop := by
  unfold spliceBytes? at h
  split at h
  · rename_i hb
    cases h
    rw [ByteArray.append_assoc]
    rw [extract_append_left (b.extract 0 offset) (val ++ b.extract (offset + val.size) b.size)
      start stop]
    · rw [extract_extract_BA]
      rw [show min (0 + stop) offset = stop by omega]
      simp
    · rw [ByteArray.size_extract]
      omega
  · simp at h

private theorem spliceBytes?_extract_after {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hafter : offset + val.size ≤ start) (hle : start ≤ stop) (hstop : stop ≤ b.size) :
    out.extract start stop = b.extract start stop := by
  unfold spliceBytes? at h
  split at h
  · rename_i hb
    cases h
    have hoff : offset ≤ b.size := by omega
    rw [extract_append_right_window (b.extract 0 offset ++ val)
      (b.extract (offset + val.size) b.size) start stop]
    · rw [ByteArray.size_append, ByteArray.size_extract]
      rw [show min offset b.size = offset by omega]
      simp only [Nat.sub_zero]
      rw [extract_extract_BA]
      rw [show offset + val.size + (start - (offset + val.size)) = start by omega]
      rw [show min (offset + val.size + (stop - (offset + val.size))) b.size = stop by omega]
    · rw [ByteArray.size_append, ByteArray.size_extract]
      rw [show min offset b.size = offset by omega]
      omega
  · simp at h

private theorem spliceBytes?_extract_disjoint {b val out : ByteArray} {offset start stop : Nat}
    (h : spliceBytes? b offset val = some out)
    (hdisj : stop ≤ offset ∨ offset + val.size ≤ start) (hle : start ≤ stop)
    (hstop : stop ≤ b.size) :
    out.extract start stop = b.extract start stop := by
  rcases hdisj with hbefore | hafter
  · exact spliceBytes?_extract_before h hbefore
  · exact spliceBytes?_extract_after h hafter hle hstop

private theorem spliceBytes?_size_eq {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    out.size = b.size := by
  unfold spliceBytes? at h
  split at h
  · rename_i hb
    cases h
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  · simp at h

private theorem patchRuntime_extract_eq_aux (ps : List (Nat × ByteArray))
    {template acc out : ByteArray} {start stop : Nat}
    (hextract : acc.extract start stop = template.extract start stop)
    (hsize : acc.size = template.size)
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : ps.foldlM (fun acc p =>
      if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none) acc = some out) :
    out.extract start stop = template.extract start stop ∧ out.size = template.size := by
  induction ps generalizing acc with
  | nil =>
      simp at h
      cases h
      exact ⟨hextract, hsize⟩
  | cons p ps ih =>
      simp only [List.foldlM_cons] at h
      by_cases hszp : p.2.size = 32
      · rw [if_pos hszp] at h
        cases hsp : spliceBytes? acc p.1 p.2 with
        | none => simp [hsp] at h
        | some acc' =>
            simp [hsp] at h
            have hdisj' : stop ≤ p.1 ∨ p.1 + p.2.size ≤ start := by
              simpa [hszp] using hdisj p (by simp)
            have hacc' : acc'.extract start stop = template.extract start stop := by
              rw [spliceBytes?_extract_disjoint hsp hdisj' hle (by rw [hsize]; exact hstop)]
              exact hextract
            have hsize' : acc'.size = template.size := by
              rw [spliceBytes?_size_eq hsp, hsize]
            exact ih hacc' hsize'
              (fun q hq => hdisj q (List.mem_cons_of_mem p hq)) h
      · rw [if_neg hszp] at h
        simp at h

theorem patchRuntime_extract_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {start stop : Nat}
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : patchRuntime template ps = some out) :
    out.extract start stop = template.extract start stop := by
  unfold patchRuntime at h
  exact (patchRuntime_extract_eq_aux ps (template := template) (acc := template)
    (out := out) (start := start) (stop := stop) rfl rfl hle hstop hdisj h).1

private theorem spliceBytes?_extract_patch {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    out.extract offset (offset + val.size) = val := by
  unfold spliceBytes? at h
  split at h
  · rename_i hb
    cases h
    rw [ByteArray.append_assoc]
    rw [extract_append_right_window (b.extract 0 offset)
      (val ++ b.extract (offset + val.size) b.size) offset (offset + val.size)]
    · rw [ByteArray.size_extract]
      have hoff : offset ≤ b.size := by omega
      rw [show min offset b.size = offset by omega]
      rw [show offset - (offset - 0) = 0 by omega]
      rw [show offset + val.size - (offset - 0) = val.size by omega]
      rw [extract_append_left val (b.extract (offset + val.size) b.size) 0 val.size]
      · exact byteArray_extract_self val
      · omega
    · rw [ByteArray.size_extract]
      omega
  · simp at h

private theorem spliceBytes?_offset_add_size_le {b val out : ByteArray} {offset : Nat}
    (h : spliceBytes? b offset val = some out) :
    offset + val.size ≤ b.size := by
  unfold spliceBytes? at h
  split at h
  · assumption
  · simp at h

private theorem patchRuntime_size_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)}
    (h : patchRuntime template ps = some out) :
    out.size = template.size := by
  unfold patchRuntime at h
  exact (patchRuntime_extract_eq_aux ps (template := template) (acc := template)
    (out := out) (start := 0) (stop := 0) rfl rfl (by omega) (by omega)
    (fun p hp => Or.inl (by omega)) h).2

theorem patchRuntime_extract_patch {template out value : ByteArray}
    {pre post : List (Nat × ByteArray)} {offset : Nat}
    (hvalue : value.size = 32)
    (hpost : ∀ p ∈ post, offset + 32 ≤ p.1 ∨ p.1 + 32 ≤ offset)
    (h : patchRuntime template (pre ++ (offset, value) :: post) = some out) :
    out.extract offset (offset + 32) = value := by
  unfold patchRuntime at h
  rw [List.foldlM_append] at h
  cases hpre : List.foldlM
      (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none)
      template pre with
  | none => simp [hpre] at h
  | some accPre =>
      simp [hpre, hvalue] at h
      cases hsp : spliceBytes? accPre offset value with
      | none => simp [hsp] at h
      | some accTarget =>
          simp [hsp] at h
          have htarget : accTarget.extract offset (offset + 32) = value := by
            simpa [hvalue] using spliceBytes?_extract_patch hsp
          have htargetSize : offset + 32 ≤ accTarget.size := by
            rw [spliceBytes?_size_eq hsp]
            simpa [hvalue] using spliceBytes?_offset_add_size_le hsp
          have htail := patchRuntime_extract_eq_aux post (template := accTarget)
            (acc := accTarget) (out := out) (start := offset) (stop := offset + 32)
            rfl rfl (by omega) htargetSize hpost h
          exact htail.1.trans htarget

private theorem patchRuntime_extract'_eq {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {start stop : Nat}
    (hle : start ≤ stop) (hstop : stop ≤ template.size)
    (hstart64 : start < 2 ^ 64) (hstop64 : stop < 2 ^ 64)
    (hdisj : ∀ p ∈ ps, stop ≤ p.1 ∨ p.1 + 32 ≤ start)
    (h : patchRuntime template ps = some out) :
    out.extract' start stop = template.extract' start stop := by
  unfold ByteArray.extract'
  have hguard : (decide (start < 2 ^ 64) && decide (stop < 2 ^ 64)) = true := by
    rw [decide_eq_true hstart64, decide_eq_true hstop64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact patchRuntime_extract_eq hle hstop hdisj h

theorem get?_eq_of_extract_one {a b : ByteArray} {idx : Nat}
    (ha : idx < a.size) (hb : idx < b.size)
    (h : a.extract idx (idx + 1) = b.extract idx (idx + 1)) :
    a.get? idx = b.get? idx := by
  unfold ByteArray.get?
  simp only [dif_pos ha, dif_pos hb]
  have hdata := congrArg ByteArray.data h
  have hlist := congrArg Array.toList hdata
  rw [ByteArray.data_extract, ByteArray.data_extract, Array.toList_extract,
    Array.toList_extract, List.extract_eq_take_drop, List.extract_eq_take_drop] at hlist
  have hleft : (List.take (idx + 1 - idx) (List.drop idx a.data.toList))[0]? =
      some (a.get idx ha) := by
    simp [ByteArray.get]
  have hright : (List.take (idx + 1 - idx) (List.drop idx b.data.toList))[0]? =
      some (b.get idx hb) := by
    simp [ByteArray.get]
  have hget := congrArg (fun xs : List UInt8 => xs[0]?) hlist
  change (List.take (idx + 1 - idx) (List.drop idx a.data.toList))[0]? =
      (List.take (idx + 1 - idx) (List.drop idx b.data.toList))[0]? at hget
  rw [hleft, hright] at hget
  exact hget

theorem uniswapV3PoolPatchedSize {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.size = uniswapV3PoolBytecode.size :=
  patchRuntime_size_eq hpatch

theorem uniswapV3PoolToken0PatchWord {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.extract 2258 2290 = UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)
  let pre : List (Nat × ByteArray) :=
    [(8315, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (8829, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (10457, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat))]
  let post : List (Nat × ByteArray) :=
    [(4853, value), (6740, value), (7822, value), (9150, value), (15650, value),
     (4551, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (6789, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (7924, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (9284, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (10529, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (15979, UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)),
     (3311, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6603, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6658, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (10565, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (3072, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (10493, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19402, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19452, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (8174, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19295, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19350, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (11259, UInt256.toByteArray (EVM.Word.ofNat v.original.toNat))]
  have hpatch' : patchRuntime uniswapV3PoolBytecode (pre ++ (2258, value) :: post) =
      some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 2258 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 2258 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch hsize hpost hpatch'

theorem uniswapV3PoolToken0ConstDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨2257⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.token0.toNat, 32)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 2257 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 2257 } : UInt256).toNat := by
    change code.get? 2257 = uniswapV3PoolBytecode.get? 2257
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 2257) (stop := 2258)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (fun p hp => by
          have hge := uniswapV3Pool_patches_ge_2258 v p hp
          exact Or.inl (by omega)) hpatch
  have hextract : code.extract' ({ val := 2257 } : UInt256).toNat.succ
      (({ val := 2257 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat) := by
    change code.extract' 2258 2290 =
      UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)
    unfold ByteArray.extract'
    have hguard : (decide (2258 < 2 ^ 64) && decide (2290 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact uniswapV3PoolToken0PatchWord hpatch
  have hgetSome : code.get? ({ val := 2257 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 2257 } : UInt256).toNat.succ
          (({ val := 2257 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.token0.toNat, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem uniswapV3PoolToken0GetterJumpdestDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨2256⟩ = some (.JUMPDEST, .none) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 2256 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 2256 } : UInt256).toNat := by
    change code.get? 2256 = uniswapV3PoolBytecode.get? 2256
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 2256) (stop := 2257)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (fun p hp => by
          have hge := uniswapV3Pool_patches_ge_2258 v p hp
          exact Or.inl (by omega)) hpatch
  have hgetSome : code.get? ({ val := 2256 } : UInt256).toNat = some 0x5b := by
    rw [hget]
    native_decide
  have hparse : (some (0x5b : UInt8) >>= parseInstr) = some .JUMPDEST := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.JUMPDEST, none) = some (Operation.JUMPDEST, none)
  rfl

theorem uniswapV3PoolToken1PatchWord {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    code.extract 10529 10561 = UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat) := by
  let value0 := UInt256.toByteArray (EVM.Word.ofNat v.token0.toNat)
  let value1 := UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)
  let pre : List (Nat × ByteArray) :=
    [(8315, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (8829, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (10457, UInt256.toByteArray (EVM.Word.ofNat v.factory.toNat)),
     (2258, value0), (4853, value0), (6740, value0), (7822, value0),
     (9150, value0), (15650, value0),
     (4551, value1), (6789, value1), (7924, value1), (9284, value1)]
  let post : List (Nat × ByteArray) :=
    [(15979, value1),
     (3311, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6603, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (6658, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (10565, UInt256.toByteArray (EVM.wordOfInt v.fee)),
     (3072, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (10493, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19402, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (19452, UInt256.toByteArray (EVM.wordOfInt v.tickSpacing)),
     (8174, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19295, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (19350, UInt256.toByteArray (EVM.wordOfInt v.maxLiquidityPerTick)),
     (11259, UInt256.toByteArray (EVM.Word.ofNat v.original.toNat))]
  have hpatch' : patchRuntime uniswapV3PoolBytecode (pre ++ (10529, value1) :: post) =
      some code := by
    dsimp [pre, post, value0, value1]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 10529 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 10529 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals omega
  have hsize : value1.size = 32 := by
    dsimp [value1]
    exact toByteArray_size _
  exact patchRuntime_extract_patch hsize hpost hpatch'

theorem uniswapV3PoolToken1ConstDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10528⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.token1.toNat, 32)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? ({ val := 10528 } : UInt256).toNat =
      uniswapV3PoolBytecode.get? ({ val := 10528 } : UInt256).toNat := by
    change code.get? 10528 = uniswapV3PoolBytecode.get? 10528
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 10528) (stop := 10529)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (fun p hp => by
          simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
            List.lookup] at hp
          rcases hp with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl
          all_goals omega) hpatch
  have hextract : code.extract' ({ val := 10528 } : UInt256).toNat.succ
      (({ val := 10528 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat) := by
    change code.extract' 10529 10561 =
      UInt256.toByteArray (EVM.Word.ofNat v.token1.toNat)
    unfold ByteArray.extract'
    have hguard : (decide (10529 < 2 ^ 64) && decide (10561 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact uniswapV3PoolToken1PatchWord hpatch
  have hgetSome : code.get? ({ val := 10528 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 10528 } : UInt256).toNat.succ
          (({ val := 10528 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.token1.toNat, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem uniswapV3PoolDecodePatchedNoArg {v : PoolImmutables} {code : ByteArray}
    {pc : UInt256} {byte : UInt8} {op : Operation}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 1 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 1 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some byte)
    (hparse : (some byte >>= parseInstr) = some op)
    (harg : argOnNBytesOfInstr op = 0) :
    decode code pc = some (op, .none) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) hwin hdisj hpatch
  unfold decode
  rw [hget, hgetTemplate, hparse]
  simp [harg]

theorem uniswapV3PoolToken1GetterJumpdestDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10527⟩ = some (.JUMPDEST, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10527⟩) (byte := 0x5b)
    (op := .JUMPDEST) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10528 ≤ p.1 ∨ p.1 + 32 ≤ 10527
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolToken1GetterDupDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10561⟩ = some (.DUP2, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10561⟩) (byte := 0x81)
    (op := .DUP2) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10562 ≤ p.1 ∨ p.1 + 32 ≤ 10561
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolToken1GetterJumpDecode {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    decode code ⟨10562⟩ = some (.JUMP, .none) := by
  refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨10562⟩) (byte := 0x56)
    (op := .JUMP) hpatch (by native_decide) ?_ (by native_decide)
    (by native_decide) (by native_decide)
  change ∀ p ∈ patches v, 10563 ≤ p.1 ∨ p.1 + 32 ≤ 10562
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

theorem uniswapV3PoolReturnAddress443Wf {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcReturnAddressFromMemWf code ⟨443⟩ := by
  dsimp [solcReturnAddressFromMemWf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide

theorem accountAddressWord_toNat (a : AccountAddress) :
    (EVM.Word.ofNat a.toNat).toNat = a.toNat := by
  unfold EVM.Word.ofNat UInt256.ofNat UInt256.toNat
  exact Nat.mod_eq_of_lt
    (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))

theorem uniswapV3PoolAddressValueTransport (a : AccountAddress) :
    some [Value.address (AccountAddress.ofNat a.toNat)] =
      some [Value.address (AccountAddress.ofNat
        (UInt256.land (EVM.Word.ofNat a.toNat) solcAddrMask).toNat)] := by
  have hword := accountAddressWord_toNat a
  have hcanon : (EVM.Word.ofNat a.toNat).toNat < EVM.addressModulus := by
    rw [hword]
    change a.toNat < EVM.twoPow 160
    simp [EVM.twoPow, AccountAddress.size]
  rw [solcAddrMask_clean hcanon, hword]

theorem uniswapV3PoolAddrLitEval {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} (a : EVM.Address) :
    evalExpr? (config v) { contract := contract v, locals := ∅ }
      (initState cA gh bl σ σ₀ g A I) (addrLit a) =
      .ok (Value.address (AccountAddress.ofNat a.toNat)) := by
  dsimp [addrLit]
  have hint :
      evalExpr? (config v) { contract := contract v, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I) (.intLit (↑↑a)) =
        .ok (.int (↑↑a)) := by
    simp [evalExpr?, pure]
  unfold evalExpr?
  rw [hint]
  change (if (↑↑a : Int) < 0 then EvalResult.error EvalError.typeError
      else EvalResult.ok
        (Value.address (AccountAddress.ofNat (Int.toNat (↑↑a : Int))))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat ↑a))
  rw [if_neg (by omega)]
  simp

/- LIBRARY CANDIDATE: composes `solcConstGetterWf` with `solcReturnAddressFromMemWf`
   for immutable address getters. -/
theorem RD.solcAddressConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnAddressFromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnAddressFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
    (solcReturnMem_read128 (UInt256.land val solcAddrMask))
    (by simp only [List.length_singleton]; omega)

theorem uniswapV3PoolDecodePatchedEqTemplateDisjoint {v : PoolImmutables} {code : ByteArray}
    {pc : UInt256} (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 33 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have hpc : pc.toNat < uniswapV3PoolBytecode.size := by omega
  have hpcCode : pc.toNat < code.size := by rw [hsize]; exact hpc
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one hpcCode hpc
    exact patchRuntime_extract_eq (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl (by omega)
        · exact Or.inr hafter)
      hpatch
  unfold decode
  rw [hget]
  cases hbyte : uniswapV3PoolBytecode.get? pc.toNat with
  | none => simp
  | some b =>
      cases hinstr : parseInstr b with
      | none => simp [hinstr]
      | some instr =>
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [hinstr, harg]
          · simp [hinstr, harg]
            have hextract :
                code.extract' pc.toNat.succ (pc.toNat.succ + argOnNBytesOfInstr instr) =
                  uniswapV3PoolBytecode.extract' pc.toNat.succ
                    (pc.toNat.succ + argOnNBytesOfInstr instr) := by
              exact patchRuntime_extract'_eq
                (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
                (start := pc.toNat.succ)
                (stop := pc.toNat.succ + argOnNBytesOfInstr instr)
                (by omega)
                (by
                  have := argOnNBytesOfInstr_le_32 instr
                  omega)
                (by omega)
                (by
                  have := argOnNBytesOfInstr_le_32 instr
                  omega)
                (fun p hp => by
                  rcases hdisj p hp with hbefore | hafter
                  · exact Or.inl (by
                      have := argOnNBytesOfInstr_le_32 instr
                      omega)
                  · exact Or.inr (by omega))
                hpatch
            rw [hextract]

private theorem lt_size_of_get?_bind_parseInstr_some {c : ByteArray} {i : ℕ}
    {instr : Operation} (h : c.get? i >>= parseInstr = some instr) : i < c.size := by
  rcases hb : c.get? i with _ | b
  · rw [hb] at h
    simp at h
  · rw [ByteArray.get?] at hb
    split at hb
    · assumption
    · simp at hb

set_option linter.unusedVariables false in
def D_J_auxPreservesTargetBool (template : ByteArray) (offsets : List Nat)
    (target : UInt256) (i : Nat) : Bool :=
  offsets.all (fun offset => decide (i + 1 ≤ offset ∨ offset + 32 ≤ i)) &&
    match hget : template.get? i >>= parseInstr with
    | none => false
    | some instr =>
        if instr = .JUMPDEST ∧ UInt256.ofNat i = target then
          true
        else
          D_J_auxPreservesTargetBool template offsets target (N i instr)
termination_by template.size - i
decreasing_by
  have hN : i < N i instr := by
    simp [N]
    omega
  have hi : i < template.size :=
    lt_size_of_get?_bind_parseInstr_some hget
  omega

private theorem patchRuntime_parse_eq_of_disjoint {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {i : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hdisj : ∀ p ∈ ps, i + 1 ≤ p.1 ∨ p.1 + 32 ≤ i) :
    out.get? i >>= parseInstr = template.get? i >>= parseInstr := by
  by_cases hi : i < template.size
  · have hsize := patchRuntime_size_eq hpatch
    have hget : out.get? i = template.get? i := by
      apply get?_eq_of_extract_one (by rw [hsize]; exact hi) hi
      exact patchRuntime_extract_eq (by omega) (by omega) hdisj hpatch
    rw [hget]
  · have hsize := patchRuntime_size_eq hpatch
    have hout : out.get? i = none := by
      rw [ByteArray.get?, dif_neg]
      rw [hsize]
      omega
    have htemplate : template.get? i = none := by
      rw [ByteArray.get?, dif_neg]
      omega
    rw [hout, htemplate]

private theorem D_J_aux_contains_push_target {code : ByteArray} {i : Nat}
    {result : Array UInt256} :
    (D_J_aux code (N i .JUMPDEST) (result.push (UInt256.ofNat i))).contains
      (UInt256.ofNat i) = true := by
  rw [D_J_aux_acc]
  rw [Array.contains_iff_mem]
  simp

theorem D_J_aux_contains_of_patchRuntime_preservesTarget {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {offsets : List Nat} {target : UInt256} {i : Nat}
    {result : Array UInt256}
    (hpatch : patchRuntime template ps = some out)
    (hoffsets : ∀ p ∈ ps, p.1 ∈ offsets)
    (hscan : D_J_auxPreservesTargetBool template offsets target i = true) :
    (D_J_aux out i result).contains target = true := by
  rw [D_J_auxPreservesTargetBool] at hscan
  cases htemplate : template.get? i >>= parseInstr with
  | none =>
      rw [htemplate] at hscan
      simp at hscan
  | some instr =>
      rw [htemplate] at hscan
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hscan
      rcases hscan with ⟨hdisj, htail⟩
      have hpatchDisj : ∀ p ∈ ps, i + 1 ≤ p.1 ∨ p.1 + 32 ≤ i := by
        intro p hp
        exact hdisj p.1 (hoffsets p hp)
      have hparse := patchRuntime_parse_eq_of_disjoint hpatch hpatchDisj
      rw [D_J_aux_eq_some out i result instr (by rw [hparse, htemplate])]
      by_cases htarget : instr = .JUMPDEST ∧ UInt256.ofNat i = target
      · rw [if_pos htarget] at htail
        rcases htarget with ⟨rfl, htarget⟩
        rw [← htarget]
        exact D_J_aux_contains_push_target
      · rw [if_neg htarget] at htail
        exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch hoffsets htail
termination_by template.size - i
decreasing_by
  have hi := lt_size_of_get?_bind_parseInstr_some htemplate
  simp [N]
  omega

def uniswapV3PoolPatchOffsets : List Nat :=
  [8315, 8829, 10457, 2258, 4853, 6740, 7822, 9150, 15650, 4551, 6789, 7924, 9284,
    10529, 15979, 3311, 6603, 6658, 10565, 3072, 10493, 19402, 19452, 8174, 19295,
    19350, 11259]

theorem uniswapV3PoolPatchOffsetMem (v : PoolImmutables) :
    ∀ p ∈ patches v, p.1 ∈ uniswapV3PoolPatchOffsets := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [uniswapV3PoolPatchOffsets]

private theorem uniswapV3PoolPatchPreservesJumpDest5293 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5293⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest6434 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨6434⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest10527 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10527⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest10599 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10599⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest10455 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10455⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5293 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5293⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5293

theorem uniswapV3PoolJumpDestPatched6434 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨6434⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest6434

theorem uniswapV3PoolJumpDestPatched10527 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10527⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest10527

theorem uniswapV3PoolJumpDestPatched10599 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10599⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest10599

theorem uniswapV3PoolJumpDestPatched10455 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10455⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest10455

theorem uniswapV3PoolJumpDestPatched2258 {v : PoolImmutables} {code : ByteArray}
    {pc : UInt256} (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : (D_J (uniswapV3PoolBytecode.extract 0 2258) 0).contains pc = true) :
    (D_J code 0).contains pc = true := by
  obtain ⟨tail, htail⟩ := uniswapV3PoolPatchedPrefix2258 hpatch
  rw [htail]
  exact D_J_contains_append_left _ _ pc h

theorem uniswapV3PoolReturn443JumpDest {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨443⟩ = true :=
  uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)

theorem uniswapV3PoolPushAtPatchedEqTemplate2258 {v : PoolImmutables} {code : ByteArray}
    {pc : UInt256} (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 33 ≤ 2258) :
    pushAt code pc = pushAt uniswapV3PoolBytecode pc := by
  unfold pushAt
  rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hwin]

theorem uniswapV3PoolArmSelNatPatchedEqTemplate2258 {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : (selArmPush4Pc pc).toNat + 33 ≤ 2258) :
    armSelNat code pc = armSelNat uniswapV3PoolBytecode pc := by
  unfold armSelNat
  rw [uniswapV3PoolPushAtPatchedEqTemplate2258 hpatch hwin]

theorem uniswapV3PoolArmTgtOpPatchedEqTemplate2258 {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : (selArmPushTgtPc pc).toNat + 33 ≤ 2258) :
    armTgtOp code pc = armTgtOp uniswapV3PoolBytecode pc := by
  unfold armTgtOp
  rw [uniswapV3PoolPushAtPatchedEqTemplate2258 hpatch hwin]

theorem uniswapV3PoolArmTgtPatchedEqTemplate2258 {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : (selArmPushTgtPc pc).toNat + 33 ≤ 2258) :
    armTgt code pc = armTgt uniswapV3PoolBytecode pc := by
  unfold armTgt
  rw [uniswapV3PoolPushAtPatchedEqTemplate2258 hpatch hwin]

theorem uniswapV3PoolArmTgtWidthPatchedEqTemplate2258 {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : (selArmPushTgtPc pc).toNat + 33 ≤ 2258) :
    armTgtWidth code pc = armTgtWidth uniswapV3PoolBytecode pc := by
  unfold armTgtWidth
  rw [uniswapV3PoolPushAtPatchedEqTemplate2258 hpatch hwin]

theorem uniswapV3PoolArmWellFormedPatched2258 {v : PoolImmutables} {code : ByteArray}
    {pc : UInt256} (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hpc : pc.toNat + 33 ≤ 2258)
    (hpush4 : (selArmPush4Pc pc).toNat + 33 ≤ 2258)
    (heqPc : (selArmEqPc pc).toNat + 33 ≤ 2258)
    (hpushT : (selArmPushTgtPc pc).toNat + 33 ≤ 2258)
    (hjumpi : (selArmJumpiPc pc (armTgtWidth uniswapV3PoolBytecode pc)).toNat + 33 ≤ 2258)
    (hwf : armWellFormed uniswapV3PoolBytecode pc) :
    armWellFormed code pc := by
  rcases hwf with ⟨hdup, hpush, heq, hop, htgt, hji⟩
  have hopEq := uniswapV3PoolArmTgtOpPatchedEqTemplate2258 hpatch hpushT
  have htgtEq := uniswapV3PoolArmTgtPatchedEqTemplate2258 hpatch hpushT
  have hwEq := uniswapV3PoolArmTgtWidthPatchedEqTemplate2258 hpatch hpushT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpc]
    exact hdup
  · rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch hpush4]
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpush4]
    exact hpush
  · rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch heqPc]
    exact heq
  · rw [hopEq]
    exact hop
  · rw [hopEq, htgtEq, hwEq]
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpushT]
    exact htgt
  · rw [hwEq]
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hjumpi]
    exact hji

theorem uniswapV3PoolSelectorSplitWellFormedPatched2258 {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hpc : pc.toNat + 33 ≤ 2258)
    (hpush4 : (selArmPush4Pc pc).toNat + 33 ≤ 2258)
    (hgtPc : (selArmEqPc pc).toNat + 33 ≤ 2258)
    (hpushT : (selArmPushTgtPc pc).toNat + 33 ≤ 2258)
    (hjumpi : (selArmJumpiPc pc (armTgtWidth uniswapV3PoolBytecode pc)).toNat + 33 ≤ 2258)
    (hwf : selectorSplitWellFormed uniswapV3PoolBytecode pc) :
    selectorSplitWellFormed code pc := by
  rcases hwf with ⟨hdup, hpush, hgt, hop, htgt, hji⟩
  have hopEq := uniswapV3PoolArmTgtOpPatchedEqTemplate2258 hpatch hpushT
  have htgtEq := uniswapV3PoolArmTgtPatchedEqTemplate2258 hpatch hpushT
  have hwEq := uniswapV3PoolArmTgtWidthPatchedEqTemplate2258 hpatch hpushT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpc]
    exact hdup
  · rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch hpush4]
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpush4]
    exact hpush
  · rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hgtPc]
    exact hgt
  · rw [hopEq]
    exact hop
  · rw [hopEq, htgtEq, hwEq]
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpushT]
    exact htgt
  · rw [hwEq]
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hjumpi]
    exact hji

theorem uniswapV3PoolFallbackRevertFrom {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hpush : decode code pc = some (.Push .PUSH2, some (⟨430⟩, 2)))
    (hjump : decode code (pc + UInt256.ofNat 3) = some (.JUMP, .none))
    (hjd : (D_J code 0).contains ⟨430⟩ = true)
    (hjdDecode : decode code ⟨430⟩ = some (.JUMPDEST, .none))
    (hr0 : decode code ⟨431⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hr1 : decode code ⟨433⟩ = some (.DUP1, .none))
    (hr2 : decode code ⟨434⟩ = some (.REVERT, .none))
    (hovPush : stk.length + 1 ≤ 1024) (hovRev : stk.length + 2 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcPush1Dup1Revert0
    (h.pushConst ⟨430⟩ (width := 2) (op := .PUSH2) (by native_decide) hpush hovPush
      |>.jump hjump hjd (by omega)
      |>.jumpdest hjdDecode (by omega))
    hr0 hr1 hr2 hovRev

theorem uniswapV3PoolSelectorArmMissTo {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc next : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (i : ℕ)
    (h : RD code I g s0 pc [solcSelectorWord I] mem aw rdata acc k C)
    (hpc : pc.toNat + 33 ≤ 2258 := by native_decide)
    (hpush4 : (selArmPush4Pc pc).toNat + 33 ≤ 2258 := by native_decide)
    (heqPc : (selArmEqPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hpushT : (selArmPushTgtPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hjumpi :
      (selArmJumpiPc pc (armTgtWidth uniswapV3PoolBytecode pc)).toNat + 33 ≤ 2258 :=
        by native_decide)
    (hwf0 : armWellFormed uniswapV3PoolBytecode pc := by
      exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide⟩)
    (hsel0 : armSelNat uniswapV3PoolBytecode pc = uniswapV3PoolSelNat i := by
      native_decide)
    (hi : i < 26 := by omega)
    (hnext : selArmNextPc pc (armTgtWidth code pc) = next := by
      rw [uniswapV3PoolArmTgtWidthPatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) :
    RD code I g s0 next [solcSelectorWord I] mem aw rdata acc (k + 5) (C + 22) := by
  have hwf : armWellFormed code pc :=
    uniswapV3PoolArmWellFormedPatched2258 hpatch hpc hpush4 heqPc hpushT hjumpi hwf0
  have heq0 : UInt256.eq (armSelNat code pc) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch hpush4, hsel0]
    simpa [uniswapV3PoolSelWord, solcSelectorWord] using
      uniswapV3PoolSelectorEq_zero I hsz hnm i hi
  have h' := h.selectorArmNotTakenAuto hwf heq0 (by simp)
  simpa [hnext] using h'

theorem uniswapV3PoolSelectorArmMissToOf {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc next : UInt256} {i : ℕ}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hmiss : (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 pc [solcSelectorWord I] mem aw rdata acc k C)
    (hpc : pc.toNat + 33 ≤ 2258 := by native_decide)
    (hpush4 : (selArmPush4Pc pc).toNat + 33 ≤ 2258 := by native_decide)
    (heqPc : (selArmEqPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hpushT : (selArmPushTgtPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hjumpi :
      (selArmJumpiPc pc (armTgtWidth uniswapV3PoolBytecode pc)).toNat + 33 ≤ 2258 :=
        by native_decide)
    (hwf0 : armWellFormed uniswapV3PoolBytecode pc := by
      exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide⟩)
    (hsel0 : armSelNat uniswapV3PoolBytecode pc = uniswapV3PoolSelNat i := by
      native_decide)
    (hi : i < 26 := by omega)
    (hnext : selArmNextPc pc (armTgtWidth code pc) = next := by
      rw [uniswapV3PoolArmTgtWidthPatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) :
    RD code I g s0 next [solcSelectorWord I] mem aw rdata acc (k + 5) (C + 22) := by
  have hwf : armWellFormed code pc :=
    uniswapV3PoolArmWellFormedPatched2258 hpatch hpc hpush4 heqPc hpushT hjumpi hwf0
  have heq0 : UInt256.eq (armSelNat code pc) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch hpush4, hsel0]
    simpa [uniswapV3PoolSelWord, solcSelectorWord] using by
      rw [uniswapV3PoolSelectorEq I hsz i hi, hmiss]
      simp
  have h' := h.selectorArmNotTakenAuto hwf heq0 (by simp)
  simpa [hnext] using h'

theorem uniswapV3PoolSelectorArmHitTo {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc target : UInt256} {i : ℕ}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hhit : (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = true)
    (h : RD code I g s0 pc [solcSelectorWord I] mem aw rdata acc k C)
    (hpc : pc.toNat + 33 ≤ 2258 := by native_decide)
    (hpush4 : (selArmPush4Pc pc).toNat + 33 ≤ 2258 := by native_decide)
    (heqPc : (selArmEqPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hpushT : (selArmPushTgtPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hjumpi :
      (selArmJumpiPc pc (armTgtWidth uniswapV3PoolBytecode pc)).toNat + 33 ≤ 2258 :=
        by native_decide)
    (hwf0 : armWellFormed uniswapV3PoolBytecode pc := by
      exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide⟩)
    (hsel0 : armSelNat uniswapV3PoolBytecode pc = uniswapV3PoolSelNat i := by
      native_decide)
    (hi : i < 26 := by omega)
    (hjd0 : (D_J (uniswapV3PoolBytecode.extract 0 2258) 0).contains
        (armTgt uniswapV3PoolBytecode pc) = true := by native_decide)
    (hnext : armTgt code pc = target := by
      rw [uniswapV3PoolArmTgtPatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) :
    RD code I g s0 target [solcSelectorWord I] mem aw rdata acc (k + 5) (C + 22) := by
  have hwf : armWellFormed code pc :=
    uniswapV3PoolArmWellFormedPatched2258 hpatch hpc hpush4 heqPc hpushT hjumpi hwf0
  have heq1 : UInt256.eq (armSelNat code pc) (solcSelectorWord I) = ⟨1⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch hpush4, hsel0]
    simpa [uniswapV3PoolSelWord, solcSelectorWord] using by
      rw [uniswapV3PoolSelectorEq I hsz i hi, hhit]
      simp
  have heqne : UInt256.eq (armSelNat code pc) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [heq1]
    decide
  have hjd : (D_J code 0).contains (armTgt code pc) = true := by
    rw [uniswapV3PoolArmTgtPatchedEqTemplate2258 hpatch hpushT]
    exact uniswapV3PoolJumpDestPatched2258 hpatch hjd0
  have h' := h.selectorArmTakenAuto hwf heqne hjd (by simp)
  simpa [hnext] using h'

theorem uniswapV3PoolSelectorSplitNotTakenTo {v : PoolImmutables}
    {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc next : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code I g s0 pc [solcSelectorWord I] mem aw rdata acc k C)
    (hgt : UInt256.gt (armSelNat code pc) (solcSelectorWord I) = ⟨0⟩)
    (hpc : pc.toNat + 33 ≤ 2258 := by native_decide)
    (hpush4 : (selArmPush4Pc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hgtPc : (selArmEqPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hpushT : (selArmPushTgtPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hjumpi :
      (selArmJumpiPc pc (armTgtWidth uniswapV3PoolBytecode pc)).toNat + 33 ≤ 2258 :=
        by native_decide)
    (hwf0 : selectorSplitWellFormed uniswapV3PoolBytecode pc := by
      exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide⟩)
    (hnext : selArmNextPc pc (armTgtWidth code pc) = next := by
      rw [uniswapV3PoolArmTgtWidthPatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) :
    RD code I g s0 next [solcSelectorWord I] mem aw rdata acc (k + 5) (C + 22) := by
  have hwf : selectorSplitWellFormed code pc :=
    uniswapV3PoolSelectorSplitWellFormedPatched2258 hpatch hpc hpush4 hgtPc hpushT
      hjumpi hwf0
  have h' := h.selectorSplitNotTakenAuto hwf hgt (by simp)
  simpa [hnext] using h'

theorem uniswapV3PoolSelectorSplitTakenTo {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc next : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code I g s0 pc [solcSelectorWord I] mem aw rdata acc k C)
    (hgt : UInt256.gt (armSelNat code pc) (solcSelectorWord I) ≠ ⟨0⟩)
    (hpc : pc.toNat + 33 ≤ 2258 := by native_decide)
    (hpush4 : (selArmPush4Pc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hgtPc : (selArmEqPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hpushT : (selArmPushTgtPc pc).toNat + 33 ≤ 2258 := by native_decide)
    (hjumpi :
      (selArmJumpiPc pc (armTgtWidth uniswapV3PoolBytecode pc)).toNat + 33 ≤ 2258 :=
        by native_decide)
    (hwf0 : selectorSplitWellFormed uniswapV3PoolBytecode pc := by
      exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide⟩)
    (hjd0 : (D_J (uniswapV3PoolBytecode.extract 0 2258) 0).contains
        (armTgt uniswapV3PoolBytecode pc) = true := by native_decide)
    (hjdWin : (armTgt uniswapV3PoolBytecode pc).toNat + 33 ≤ 2258 := by native_decide)
    (hjdDecode0 : decode uniswapV3PoolBytecode (armTgt uniswapV3PoolBytecode pc) =
        some (.JUMPDEST, .none) := by native_decide)
    (hnext : armTgt code pc + ⟨1⟩ = next := by
      rw [uniswapV3PoolArmTgtPatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) :
    RD code I g s0 next [solcSelectorWord I] mem aw rdata acc (k + 6) (C + 23) := by
  have hwf : selectorSplitWellFormed code pc :=
    uniswapV3PoolSelectorSplitWellFormedPatched2258 hpatch hpc hpush4 hgtPc hpushT
      hjumpi hwf0
  have hjd : (D_J code 0).contains (armTgt code pc) = true := by
    rw [uniswapV3PoolArmTgtPatchedEqTemplate2258 hpatch hpushT]
    exact uniswapV3PoolJumpDestPatched2258 hpatch hjd0
  have hjdDecode : decode code (armTgt code pc) = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolArmTgtPatchedEqTemplate2258 hpatch hpushT]
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hjdWin]
    exact hjdDecode0
  have h' := h.selectorSplitTakenAuto hwf hgt hjd (by simp)
  have h'' := h'.jumpdest hjdDecode (by simp)
  simpa [hnext] using h''

theorem uniswapV3PoolFallbackTailFrom {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {pc : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code I g s0 pc [solcSelectorWord I] mem aw rdata acc k C)
    (hpushWin : pc.toNat + 33 ≤ 2258 := by native_decide)
    (hjumpWin : (pc + UInt256.ofNat 3).toNat + 33 ≤ 2258 := by native_decide)
    (hpush0 : decode uniswapV3PoolBytecode pc =
        some (.Push .PUSH2, some (⟨430⟩, 2)) := by native_decide)
    (hjump0 : decode uniswapV3PoolBytecode (pc + UInt256.ofNat 3) =
        some (.JUMP, .none) := by native_decide) :
    RDrev code g s0 := by
  exact uniswapV3PoolFallbackRevertFrom h
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hpushWin]; exact hpush0)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch hjumpWin]; exact hjump0)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by simp)
    (by simp)

theorem uniswapV3PoolFallbackJumpdestFrom {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨430⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  exact RD.solcPush1Dup1Revert0
    (h.jumpdest
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by simp))
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by simp)

theorem uniswapV3PoolNoMatch_65 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨65⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h76 := uniswapV3PoolSelectorArmMissTo (next := ⟨76⟩) hpatch hsz hnm 22 h
  have h87 := uniswapV3PoolSelectorArmMissTo (next := ⟨87⟩) hpatch hsz hnm 23 h76
  have h98 := uniswapV3PoolSelectorArmMissTo (next := ⟨98⟩) hpatch hsz hnm 24 h87
  have h109 := uniswapV3PoolSelectorArmMissTo (next := ⟨109⟩) hpatch hsz hnm 25 h98
  exact uniswapV3PoolFallbackTailFrom hpatch h109

theorem uniswapV3PoolNoMatch_114 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨114⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h125 := uniswapV3PoolSelectorArmMissTo (next := ⟨125⟩) hpatch hsz hnm 19 h
  have h136 := uniswapV3PoolSelectorArmMissTo (next := ⟨136⟩) hpatch hsz hnm 20 h125
  have h147 := uniswapV3PoolSelectorArmMissTo (next := ⟨147⟩) hpatch hsz hnm 21 h136
  exact uniswapV3PoolFallbackTailFrom hpatch h147

theorem uniswapV3PoolNoMatch_163 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨163⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h174 := uniswapV3PoolSelectorArmMissTo (next := ⟨174⟩) hpatch hsz hnm 16 h
  have h185 := uniswapV3PoolSelectorArmMissTo (next := ⟨185⟩) hpatch hsz hnm 17 h174
  have h196 := uniswapV3PoolSelectorArmMissTo (next := ⟨196⟩) hpatch hsz hnm 18 h185
  exact uniswapV3PoolFallbackTailFrom hpatch h196

theorem uniswapV3PoolNoMatch_201 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨201⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h212 := uniswapV3PoolSelectorArmMissTo (next := ⟨212⟩) hpatch hsz hnm 13 h
  have h223 := uniswapV3PoolSelectorArmMissTo (next := ⟨223⟩) hpatch hsz hnm 14 h212
  have h234 := uniswapV3PoolSelectorArmMissTo (next := ⟨234⟩) hpatch hsz hnm 15 h223
  exact uniswapV3PoolFallbackTailFrom hpatch h234

theorem uniswapV3PoolNoMatch_261 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨261⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h272 := uniswapV3PoolSelectorArmMissTo (next := ⟨272⟩) hpatch hsz hnm 9 h
  have h283 := uniswapV3PoolSelectorArmMissTo (next := ⟨283⟩) hpatch hsz hnm 10 h272
  have h294 := uniswapV3PoolSelectorArmMissTo (next := ⟨294⟩) hpatch hsz hnm 11 h283
  have h305 := uniswapV3PoolSelectorArmMissTo (next := ⟨305⟩) hpatch hsz hnm 12 h294
  exact uniswapV3PoolFallbackTailFrom hpatch h305

theorem uniswapV3PoolNoMatch_310 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨310⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h321 := uniswapV3PoolSelectorArmMissTo (next := ⟨321⟩) hpatch hsz hnm 6 h
  have h332 := uniswapV3PoolSelectorArmMissTo (next := ⟨332⟩) hpatch hsz hnm 7 h321
  have h343 := uniswapV3PoolSelectorArmMissTo (next := ⟨343⟩) hpatch hsz hnm 8 h332
  exact uniswapV3PoolFallbackTailFrom hpatch h343

theorem uniswapV3PoolNoMatch_359 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨359⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h370 := uniswapV3PoolSelectorArmMissTo (next := ⟨370⟩) hpatch hsz hnm 3 h
  have h381 := uniswapV3PoolSelectorArmMissTo (next := ⟨381⟩) hpatch hsz hnm 4 h370
  have h392 := uniswapV3PoolSelectorArmMissTo (next := ⟨392⟩) hpatch hsz hnm 5 h381
  exact uniswapV3PoolFallbackTailFrom hpatch h392

theorem uniswapV3PoolNoMatch_397 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨397⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h408 := uniswapV3PoolSelectorArmMissTo (next := ⟨408⟩) hpatch hsz hnm 0 h
  have h419 := uniswapV3PoolSelectorArmMissTo (next := ⟨419⟩) hpatch hsz hnm 1 h408
  have h430 := uniswapV3PoolSelectorArmMissTo (next := ⟨430⟩) hpatch hsz hnm 2 h419
  exact uniswapV3PoolFallbackJumpdestFrom hpatch h430

theorem uniswapV3PoolNoMatch_54 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨54⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  by_cases hgt : UInt256.gt (armSelNat code ⟨54⟩) (solcSelectorWord I) = ⟨0⟩
  · have h65 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨65⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_65 hpatch hsz hnm h65
  · have h114 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨114⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_114 hpatch hsz hnm h114

theorem uniswapV3PoolNoMatch_152 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨152⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  by_cases hgt : UInt256.gt (armSelNat code ⟨152⟩) (solcSelectorWord I) = ⟨0⟩
  · have h163 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨163⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_163 hpatch hsz hnm h163
  · have h201 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨201⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_201 hpatch hsz hnm h201

theorem uniswapV3PoolNoMatch_250 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨250⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  by_cases hgt : UInt256.gt (armSelNat code ⟨250⟩) (solcSelectorWord I) = ⟨0⟩
  · have h261 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨261⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_261 hpatch hsz hnm h261
  · have h310 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨310⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_310 hpatch hsz hnm h310

theorem uniswapV3PoolNoMatch_348 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨348⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  by_cases hgt : UInt256.gt (armSelNat code ⟨348⟩) (solcSelectorWord I) = ⟨0⟩
  · have h359 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨359⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_359 hpatch hsz hnm h359
  · have h397 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨397⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_397 hpatch hsz hnm h397

theorem uniswapV3PoolNoMatch_43 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨43⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  by_cases hgt : UInt256.gt (armSelNat code ⟨43⟩) (solcSelectorWord I) = ⟨0⟩
  · have h54 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨54⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_54 hpatch hsz hnm h54
  · have h152 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨152⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_152 hpatch hsz hnm h152

theorem uniswapV3PoolNoMatch_239 {v : PoolImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g s0 ⟨239⟩ [solcSelectorWord I] mem aw rdata acc k C) :
    RDrev code g s0 := by
  by_cases hgt : UInt256.gt (armSelNat code ⟨239⟩) (solcSelectorWord I) = ⟨0⟩
  · have h250 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨250⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_250 hpatch hsz hnm h250
  · have h348 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨348⟩) hpatch h hgt
    exact uniswapV3PoolNoMatch_348 hpatch hsz hnm h348

set_option maxHeartbeats 3000000 in
theorem uniswapV3PoolReachSelector32 {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨32⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact solcLegacyDispatchReachSelector
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (bodyPc := ⟨18⟩) (loadPc := ⟨26⟩) (firstPc := ⟨32⟩)
    (guardTgt := ⟨16⟩) (revertTgt := ⟨430⟩) (guardWidth := 2) (revertWidth := 2)
    (guardOp := .PUSH2) (revertOp := .PUSH2)
    hcode hwv hsz hsize
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)

set_option maxHeartbeats 3000000 in
theorem uniswapV3PoolX_noMatch {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h32⟩ := solcLegacyDispatchReachSelector
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (bodyPc := ⟨18⟩) (loadPc := ⟨26⟩) (firstPc := ⟨32⟩)
    (guardTgt := ⟨16⟩) (revertTgt := ⟨430⟩) (guardWidth := 2) (revertWidth := 2)
    (guardOp := .PUSH2) (revertOp := .PUSH2)
    hcode hwv hsz hsize
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by native_decide)
  by_cases hgt : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) = ⟨0⟩
  · have h43 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨43⟩) hpatch h32 hgt
    exact uniswapV3PoolNoMatch_43 hpatch hsz hnm h43
  · have h239 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨239⟩) hpatch h32 hgt
    exact uniswapV3PoolNoMatch_239 hpatch hsz hnm h239

/-- Calldata shorter than a selector dispatches to no transition. -/
theorem uniswapV3PoolDispatch_none_short (v : PoolImmutables) {cd : ByteArray}
    (h : cd.size < 4) :
    dispatchMsg (contract v) cd = none := by
  rw [dispatchMsg_eq_dispatchList (contract v) cd (by rfl)]
  change dispatchList
    [ burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v,
      observationsTransition, observeTransition v, positionsTransition, protocolfeesTransition,
      setfeeprotocolTransition v, slot0Transition, snapshotcumulativesinsideTransition v,
      swapTransition v, tickbitmapTransition, tickspacingTransition v, ticksTransition,
      token0Transition v, token1Transition v ] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]; rfl
    · rw [selectorOf, collectSelectorBytes v]; rfl
    · rw [selectorOf, collectProtocolSelectorBytes v]; rfl
    · rw [selectorOf, factorySelectorBytes v]; rfl
    · rw [selectorOf, feeSelectorBytes v]; rfl
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]; rfl
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]; rfl
    · rw [selectorOf, flashSelectorBytes v]; rfl
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]; rfl
    · rw [selectorOf, initializeSelectorBytes]; rfl
    · rw [selectorOf, liquiditySelectorBytes]; rfl
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]; rfl
    · rw [selectorOf, mintSelectorBytes v]; rfl
    · rw [selectorOf, observationsSelectorBytes]; rfl
    · rw [selectorOf, observeSelectorBytes v]; rfl
    · rw [selectorOf, positionsSelectorBytes]; rfl
    · rw [selectorOf, protocolFeesSelectorBytes]; rfl
    · rw [selectorOf, setFeeProtocolSelectorBytes v]; rfl
    · rw [selectorOf, slot0SelectorBytes]; rfl
    · rw [selectorOf, snapshotCumulativesInsideSelectorBytes v]; rfl
    · rw [selectorOf, swapSelectorBytes v]; rfl
    · rw [selectorOf, tickBitmapSelectorBytes]; rfl
    · rw [selectorOf, tickSpacingSelectorBytes v]; rfl
    · rw [selectorOf, ticksSelectorBytes]; rfl
    · rw [selectorOf, token0SelectorBytes v]; rfl
    · rw [selectorOf, token1SelectorBytes v]; rfl) h

/-- If none of the public selectors match, dispatch yields no transition. -/
theorem uniswapV3PoolDispatch_none_nomatch (v : PoolImmutables) {cd : ByteArray}
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg (contract v) cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, burnSelectorBytes]; simpa [uniswapV3PoolSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, collectSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, collectProtocolSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, factorySelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, feeSelectorBytes v]; simpa [uniswapV3PoolSelBytes] using hnm 22 (by omega)
  · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 23 (by omega)
  · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, flashSelectorBytes v]; simpa [uniswapV3PoolSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, initializeSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 25 (by omega)
  · rw [selectorOf, liquiditySelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, mintSelectorBytes v]; simpa [uniswapV3PoolSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, observationsSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, observeSelectorBytes v]; simpa [uniswapV3PoolSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, positionsSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, protocolFeesSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, setFeeProtocolSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, slot0SelectorBytes]; simpa [uniswapV3PoolSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, snapshotCumulativesInsideSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, swapSelectorBytes v]; simpa [uniswapV3PoolSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, tickBitmapSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, tickSpacingSelectorBytes v]
    simpa [uniswapV3PoolSelBytes] using hnm 20 (by omega)
  · rw [selectorOf, ticksSelectorBytes]; simpa [uniswapV3PoolSelBytes] using hnm 24 (by omega)
  · rw [selectorOf, token0SelectorBytes v]; simpa [uniswapV3PoolSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, token1SelectorBytes v]; simpa [uniswapV3PoolSelBytes] using hnm 21 (by omega)

theorem uniswapV3PoolNoDispatch {v : PoolImmutables} {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hnm : ∀ i, i < 26 → (uniswapV3PoolSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (uniswapV3PoolX_noMatch (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hnm)
    |>.reEquivNoDispatch hcode (uniswapV3PoolDispatch_none_nomatch v hnm)

theorem uniswapV3PoolBodyReverts_nonPayable (v : PoolImmutables)
    (t : TransitionDecl) (ht : t ∈ (contract v).transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

set_option maxHeartbeats 2000000 in
theorem uniswapV3PoolX_callvalue_ne {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
  exact RD.solcPush1Dup1Revert0
    (h0.pushConst (solcGuardTgt uniswapV3PoolBytecode)
      (width := solcGuardTgtWidth uniswapV3PoolBytecode)
      (op := solcGuardTgtOp uniswapV3PoolBytecode)
      (by native_decide)
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by simp only [List.length]; omega)
      |>.jumpiNT
        (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
        (isZero_eq_zero_of_ne hwv)
        (by simp only [List.length]; omega))
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by simp only [List.length]; omega)

set_option maxHeartbeats 2000000 in
theorem uniswapV3PoolX_short {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt uniswapV3PoolBytecode)
    (opC := solcGuardTgtOp uniswapV3PoolBytecode)
    (wC := solcGuardTgtWidth uniswapV3PoolBytecode) h0 hwv
    (by native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
  exact RD.solcPush1Dup1Revert0
    (h1.push1 ⟨4⟩
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by simp only [List.length]; omega)
      |>.calldatasize
        (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
        (by simp only [List.length]; omega)
      |>.lt
        (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
        (by simp only [List.length]; omega)
      |>.pushConst (solcCalldataRevertTgt uniswapV3PoolBytecode)
        (width := solcCalldataRevertTgtWidth uniswapV3PoolBytecode)
        (op := solcCalldataRevertTgtOp uniswapV3PoolBytecode)
        (by native_decide)
        (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
        (by simp only [List.length]; omega)
      |>.jumpiT
        (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
        (lt_four_ne_zero_of_lt hsz)
        (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
        (by simp only [List.length]; omega)
      |>.jumpdest
        (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
        (by simp only [List.length]; omega))
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by simp only [List.length]; omega)

theorem uniswapV3PoolShortRevert {v : PoolImmutables} {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code)
    (_hsize : I.calldata.size < UInt256.size) (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (uniswapV3PoolX_short (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz)
    |>.reEquivNoDispatch hcode (uniswapV3PoolDispatch_none_short v hsz)

theorem uniswapV3PoolNonPayable {v : PoolImmutables} {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (uniswapV3PoolX_callvalue_ne (g := Sat256.ofUInt256 g) hpatch hcode hwv)
    |>.reEquivElim hcode
      fun _ _ hrev => by
        by_cases hdisp : dispatchMsg (contract v) I.calldata = none
        · exact reEquiv_noDispatch hdisp hrev
        · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
          have htmem : t ∈ (contract v).transitions := by
            rw [dispatchMsg_eq_dispatchList (contract v) I.calldata (by rfl)] at ht
            exact dispatchList_some_mem ht
          by_cases hdec : decodeCalldataWithMode (config v).abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none
          · exact reEquiv_decodingFailed ht hdec hrev
          · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
            exact reEquiv_execution ht hca
              (uniswapV3PoolBodyReverts_nonPayable v t htmem
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
                (by simp only [initState]; exact hwv))
              (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

end Benchmarks.UniswapV3Pool
