import Benchmarks.UniswapV3.Pool.ConstructorMemory
import Benchmarks.UniswapV3.Pool.DisjointWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def constructorPatchSites : List (Nat × String) :=
  [(8174, "maxLiquidityPerTick"), (19295, "maxLiquidityPerTick"), (19350, "maxLiquidityPerTick"),
   (3072, "tickSpacing"), (10493, "tickSpacing"), (19402, "tickSpacing"), (19452, "tickSpacing"),
   (3311, "fee"), (6603, "fee"), (6658, "fee"), (10565, "fee"),
   (4551, "token1"), (6789, "token1"), (7924, "token1"), (9284, "token1"),
   (10529, "token1"), (15979, "token1"),
   (2258, "token0"), (4853, "token0"), (6740, "token0"), (7822, "token0"),
   (9150, "token0"), (15650, "token0"),
   (8315, "factory"), (8829, "factory"), (10457, "factory"), (11259, "original")]

def constructorPatchWrites (words : String → UInt256) : List (Nat × UInt256) :=
  constructorPatchSites.map (fun s ↦ (s.1, words s.2))

def constructorPatchedRuntime (words : String → UInt256) : ByteArray :=
  writeCascade uniswapV3PoolBytecode (constructorPatchWrites words)

theorem constructorPatchPermutation (words : String → UInt256) :
    (constructorPatchWrites words).Perm (immutableLayout.writes words) := by
  have hp : constructorPatchSites.Perm
      (immutableLayout.sites.map (fun s ↦ (s.1, s.2.2))) := by native_decide
  exact hp.map (fun s ↦ (s.1, words s.2))

theorem constructorPatchBounds (words : String → UInt256) :
    ∀ w ∈ constructorPatchWrites words, w.1 + 32 ≤ uniswapV3PoolBytecode.size := by
  have hb : constructorPatchSites.all (fun s ↦ decide (s.1 + 32 ≤ 22142)) = true := by decide
  intro w hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
  rw [uniswapV3PoolBytecode_size]
  exact of_decide_eq_true (List.all_eq_true.mp hb s hs)

theorem constructorPatchDisjoint (words : String → UInt256) :
    ∀ x ∈ constructorPatchWrites words, ∀ y ∈ constructorPatchWrites words,
      x ≠ y → x.1 + 32 ≤ y.1 ∨ y.1 + 32 ≤ x.1 := by
  have hd : constructorPatchSites.all (fun x ↦ constructorPatchSites.all (fun y ↦
      decide (x = y ∨ x.1 + 32 ≤ y.1 ∨ y.1 + 32 ≤ x.1))) = true := by native_decide
  intro x hx y hy hn
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  have h := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hd a ha) b hb)
  rcases h with rfl | h
  · exact (hn rfl).elim
  · exact h

theorem constructorPatchedRuntime_eq (words : String → UInt256) :
    constructorPatchedRuntime words = immutableLayout.runtime uniswapV3PoolBytecode words :=
  writeCascade_perm _ (constructorPatchPermutation words) (constructorPatchBounds words)
    (constructorPatchDisjoint words)

theorem constructorPatchedRuntime_size (words : String → UInt256) :
    (constructorPatchedRuntime words).size = 22142 := by
  apply writeCascade_size_of_base _ _ uniswapV3PoolBytecode_size
  · simp only [constructorPatchWrites, constructorPatchSites, List.map_cons, List.map_nil,
      WriteGapsOk]
    norm_num [USize.size_pos]
  · simp only [constructorPatchWrites, constructorPatchSites, List.map_cons, List.map_nil,
      writeCascadeSize]
    rfl

theorem constructorRuntimeCopy (tail mem : ByteArray) (hm : mem.size ≤ 22142) :
    (uniswapV3PoolCreationBytecode ++ tail).write 586 mem 0 22142 = uniswapV3PoolBytecode := by
  have hs : uniswapV3PoolCreationBytecode.size = 22728 := by native_decide
  rw [write0_eq_extract_from_of_base_le _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, hs]; omega) hm]
  rw [byteArray_extract_append_left _ _ _ _ (by rw [hs])]
  native_decide

end Benchmarks.UniswapV3.Pool
