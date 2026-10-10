import Benchmarks.UniswapV3.Pool.SnapshotRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickOutsideTickWord (key : Int) (σ : AccountMap) (I : ExecutionEnv) :
    EVM.wordOfInt (tickOutside key σ I).cumulative =
      UInt256.signextend (UInt256.ofNat 6) (solcSlotWordAt (tickFieldSlot key 3) σ I) := by
  have h := signextend_normalizeSint ⟨56, by decide⟩ (UInt256.ofNat 6)
    (solcSlotWordAt (tickFieldSlot key 3) σ I) (by decide) (by decide)
  simpa only [tickOutside, tickSignedFieldValue, Nat.pow_zero,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, word_div_one] using h.symm

theorem tickFieldShift (key : Int) (delta offset size : Nat) (shift mask : UInt256)
    (σ : AccountMap) (I : ExecutionEnv)
    (hs : shift = UInt256.ofNat (256 ^ offset)) (hm : mask = UInt256.ofNat (256 ^ size - 1)) :
    tickFieldWord key delta offset size σ I =
      UInt256.land mask (UInt256.div (solcSlotWordAt (tickFieldSlot key delta) σ I) shift) := by
  rw [hs, hm, u256_land_comm]
  rfl

theorem tickOutsideLiquidityWord (key : Int) (σ : AccountMap) (I : ExecutionEnv) :
    (tickOutside key σ I).secondsPerLiquidity =
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
        (UInt256.div (solcSlotWordAt (tickFieldSlot key 3) σ I) (UInt256.ofNat 72057594037927936)) :=
  tickFieldShift key 3 7 20 _ _ σ I (by native_decide) (by native_decide)

theorem tickOutsideSecondsWord (key : Int) (σ : AccountMap) (I : ExecutionEnv) :
    (tickOutside key σ I).seconds = UInt256.land (UInt256.ofNat 4294967295)
      (UInt256.div (solcSlotWordAt (tickFieldSlot key 3) σ I)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216))) :=
  tickFieldShift key 3 27 4 _ _ σ I (by native_decide) (by native_decide)

theorem tickOutsideInitializedWord (key : Int) (σ : AccountMap) (I : ExecutionEnv) :
    tickFieldWord key 3 31 1 σ I = UInt256.land (UInt256.ofNat 255)
      (UInt256.div (solcSlotWordAt (tickFieldSlot key 3) σ I)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))) :=
  tickFieldShift key 3 31 1 _ _ σ I (by native_decide) (by native_decide)

theorem tickOutsideInitialized_false (key : Int) (σ : AccountMap) (I : ExecutionEnv) :
    (tickOutside key σ I).initialized = false ↔ tickFieldWord key 3 31 1 σ I = ⟨0⟩ := by
  simp [tickOutside]

theorem tickOutsideInitialized_true (key : Int) (σ : AccountMap) (I : ExecutionEnv) :
    (tickOutside key σ I).initialized = true ↔ tickFieldWord key 3 31 1 σ I ≠ ⟨0⟩ := by
  simp [tickOutside]

end Benchmarks.UniswapV3.Pool
