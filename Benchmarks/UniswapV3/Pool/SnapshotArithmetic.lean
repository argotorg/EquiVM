import Benchmarks.UniswapV3.Pool.SnapshotBranches
import Benchmarks.UniswapV3.Pool.TupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: removing an intermediate fixed-width subtraction cast.
theorem normalizeInt_sub_left (ty : ABI.IntType) (i j : Int) :
    normalizeInt ty (normalizeInt ty i - j) = normalizeInt ty (i - j) := by
  have hr : (normalizeInt ty i - j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) =
      (i - j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) := by
    rw [Int.sub_emod, normalizeInt_residue, ← Int.sub_emod]
  cases ty with
  | uint width => exact hr
  | sint width => simp only [normalizeInt, IntType.bitWidth] at hr ⊢; rw [hr]

theorem wordOfInt_normalizeUint (width : ABI.BitWidth) (i : Int) (mask : UInt256)
    (hmask : mask.toNat = 2 ^ width.val - 1) :
    EVM.wordOfInt (normalizeInt (.uint width) i) = UInt256.land (EVM.wordOfInt i) mask := by
  rw [normalizeUIntInt_mask width i mask hmask, wordOfInt_ofNat_toNat]

def SnapshotCumulatives.words (result : SnapshotCumulatives) : List UInt256 :=
  [EVM.wordOfInt result.tick, EVM.wordOfInt result.secondsPerLiquidity, EVM.wordOfInt result.seconds]
def snapshotCleanWords (seconds liquidity tick : UInt256) : List UInt256 :=
  [UInt256.signextend (UInt256.ofNat 6) tick,
   UInt256.land liquidity (UInt256.ofNat (2 ^ 160 - 1)),
   UInt256.land (UInt256.ofNat 4294967295) seconds]

theorem snapshotDifferenceWords (a b : TickOutside) :
    snapshotCleanWords (UInt256.sub a.seconds b.seconds)
      (UInt256.sub a.secondsPerLiquidity b.secondsPerLiquidity)
      (UInt256.sub (EVM.wordOfInt a.cumulative) (EVM.wordOfInt b.cumulative)) =
      (snapshotDifference a b).words := by
  simp only [snapshotCleanWords, SnapshotCumulatives.words, snapshotDifference,
    wordOfInt_normalizeUint ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide),
    wordOfInt_normalizeUint ⟨32, by decide⟩ _ (UInt256.ofNat 4294967295) (by decide),
    wordOfInt_sub, wordOfInt_ofNat_toNat]
  rw [← wordOfInt_sub, signextend_wordOfInt ⟨56, by decide⟩ _ _ (by decide) (by decide), u256_land_comm (UInt256.ofNat 4294967295)]

theorem snapshotInsideWords (current : OracleObservation) (time : UInt256) (a b : TickOutside) :
    snapshotCleanWords (UInt256.sub (UInt256.sub time a.seconds) b.seconds)
      (UInt256.sub (UInt256.sub current.secondsPerLiquidity a.secondsPerLiquidity) b.secondsPerLiquidity)
      (UInt256.sub (UInt256.sub (EVM.wordOfInt current.tickCumulative)
        (EVM.wordOfInt a.cumulative)) (EVM.wordOfInt b.cumulative)) =
      (snapshotInside current time a b).words := by
  simp only [snapshotCleanWords, SnapshotCumulatives.words, snapshotInside, normalizeInt_sub_left,
    wordOfInt_normalizeUint ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide),
    wordOfInt_normalizeUint ⟨32, by decide⟩ _ (UInt256.ofNat 4294967295) (by decide),
    wordOfInt_sub, wordOfInt_ofNat_toNat]
  rw [← wordOfInt_sub, ← wordOfInt_sub,
    signextend_wordOfInt ⟨56, by decide⟩ _ _ (by decide) (by decide), u256_land_comm (UInt256.ofNat 4294967295)]

-- LIBRARY CANDIDATE: encode an arbitrary normalized signed integer.
theorem encodeABIValue_normalizedSint (width : ABI.BitWidth) (i : Int) :
    encodeABIValue? (.elem (.int (.sint width))) (.int (normalizeInt (.sint width) i)) =
      some (EVM.Word.toBytesBE (EVM.wordOfInt (normalizeInt (.sint width) i))) := by
  simpa only [normalizeInt_wordOfInt] using encodeABIValue_sintCast width (EVM.wordOfInt i)

theorem encodeABIValue_normalizedUint (width : ABI.BitWidth) (i : Int) (mask : UInt256)
    (hmask : mask.toNat = 2 ^ width.val - 1) :
    encodeABIValue? (.elem (.int (.uint width))) (.int (normalizeInt (.uint width) i)) =
      some (EVM.Word.toBytesBE (EVM.wordOfInt (normalizeInt (.uint width) i))) := by
  rw [normalizeUIntInt_mask width i mask hmask, wordOfInt_ofNat_toNat]
  exact encodeABIValue_uint width _ (u256LandMaskToNatLtOfToNat _ _ hmask)

theorem snapshotCumulativesEncoding (c : SnapshotCumulatives)
    (ht : encodeABIValue? (.elem (.int (.sint ⟨56, by decide⟩))) (.int c.tick) =
      some (EVM.Word.toBytesBE (EVM.wordOfInt c.tick)))
    (hl : encodeABIValue? (.elem (.int (.uint ⟨160, by decide⟩))) (.int c.secondsPerLiquidity) =
      some (EVM.Word.toBytesBE (EVM.wordOfInt c.secondsPerLiquidity)))
    (hs : encodeABIValue? (.elem (.int (.uint ⟨32, by decide⟩))) (.int c.seconds) =
      some (EVM.Word.toBytesBE (EVM.wordOfInt c.seconds))) :
    encodeReturnValues? snapshotTransition.returnType c.values = some (wordBytes c.words) := by
  let items : List (ABIType × Value × EVM.Word) :=
    [(.elem (.int (.sint ⟨56, by decide⟩)), .int c.tick, EVM.wordOfInt c.tick),
     (.elem (.int (.uint ⟨160, by decide⟩)), .int c.secondsPerLiquidity, EVM.wordOfInt c.secondsPerLiquidity),
     (.elem (.int (.uint ⟨32, by decide⟩)), .int c.seconds, EVM.wordOfInt c.seconds)]
  have h := staticWordsReturnEncoding items 96
    (by simp only [items, List.map_cons, List.map_nil, abiTupleHeadSize?, staticABIEncodedSize?,
          isDynamicABIType, bind, Option.bind]; rfl)
    (by intro x hx; simp only [items, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> rfl)
    (by intro x hx; simp only [items, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ht
        · exact hl
        · exact hs)
  rw [wordBytes_eq_list]
  exact h

theorem snapshotReturnEncoding (lower upper : Int) (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? snapshotTransition.returnType (snapshotResult lower upper σ I).values =
      some (wordBytes (snapshotResult lower upper σ I).words) := by
  unfold snapshotResult
  split
  · apply snapshotCumulativesEncoding <;> dsimp only [snapshotDifference, snapshotInside]
    · exact encodeABIValue_normalizedSint ⟨56, by decide⟩ _
    · exact encodeABIValue_normalizedUint ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide)
    · exact encodeABIValue_normalizedUint ⟨32, by decide⟩ _ (UInt256.ofNat (2 ^ 32 - 1)) (by decide)
  · split
    · apply snapshotCumulativesEncoding <;> dsimp only [snapshotDifference, snapshotInside]
      · exact encodeABIValue_normalizedSint ⟨56, by decide⟩ _
      · exact encodeABIValue_normalizedUint ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide)
      · exact encodeABIValue_normalizedUint ⟨32, by decide⟩ _ (UInt256.ofNat (2 ^ 32 - 1)) (by decide)
    · apply snapshotCumulativesEncoding <;> dsimp only [snapshotDifference, snapshotInside]
      · exact encodeABIValue_normalizedSint ⟨56, by decide⟩ _
      · exact encodeABIValue_normalizedUint ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide)
      · exact encodeABIValue_normalizedUint ⟨32, by decide⟩ _ (UInt256.ofNat (2 ^ 32 - 1)) (by decide)

end Benchmarks.UniswapV3.Pool
