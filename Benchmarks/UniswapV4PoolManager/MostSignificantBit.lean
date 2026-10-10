import Benchmarks.UniswapV4PoolManager.WordShiftSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def msbInitial (x : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.lt (UInt256.ofNat (2^128-1)) x) (UInt256.ofNat 7)
def msbStage (x r limit : UInt256) (bit : Nat) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (UInt256.lt limit (UInt256.shiftRight x r)) (UInt256.ofNat bit)) r
def msb64 (x : UInt256) : UInt256 := msbStage x (msbInitial x) (UInt256.ofNat (2^64-1)) 6
def msb32 (x : UInt256) : UInt256 := msbStage x (msb64 x) (UInt256.ofNat (2^32-1)) 5
def msb16 (x : UInt256) : UInt256 := msbStage x (msb32 x) (UInt256.ofNat (2^16-1)) 4
def msbHigh (x : UInt256) : UInt256 := msbStage x (msb16 x) (UInt256.ofNat 255) 3
def msbIndex (x : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 31) (UInt256.shiftRight
    (UInt256.ofNat 175629608733387594055579892975202555070) (UInt256.shiftRight x (msbHigh x)))
def msbTable : UInt256 := UInt256.ofNat 3176832568382053640854229765616608417700587278678501850580078522814972297216
def mostSignificantBit (x : UInt256) : UInt256 := UInt256.lor (UInt256.byteAt (msbIndex x) msbTable) (msbHigh x)

-- LIBRARY CANDIDATE: a shifted boolean fits into a byte for shifts below eight.
theorem shiftComparison_lt_256 (a b : UInt256) {n : Nat} (hn : n < 8) :
    (UInt256.shiftLeft (UInt256.lt a b) (UInt256.ofNat n)).toNat < 256 := by
  rw [shiftComparison_toNat _ _ (by omega)]
  split
  · exact Nat.pow_lt_pow_right (by decide) hn
  · decide

theorem msbStage_lt_256 (x r limit : UInt256) {bit : Nat} (hb : bit < 8) (hr : r.toNat < 256) :
    (msbStage x r limit bit).toNat < 256 := by
  rw [msbStage, u256_lor_toNat_exact]
  exact Nat.or_lt_two_pow (n := 8) (shiftComparison_lt_256 _ _ hb) hr

theorem msbHigh_lt_256 (x : UInt256) : (msbHigh x).toNat < 256 :=
  msbStage_lt_256 _ _ _ (by decide) (msbStage_lt_256 _ _ _ (by decide)
    (msbStage_lt_256 _ _ _ (by decide) (msbStage_lt_256 _ _ _ (by decide)
      (shiftComparison_lt_256 _ _ (by decide)))))

-- LIBRARY CANDIDATE: EVM BYTE always returns a canonical uint8.
theorem byteAt_lt_256 (index word : UInt256) : (UInt256.byteAt index word).toNat < 256 := by
  unfold UInt256.byteAt
  split
  · decide
  · exact u256LandMaskToNatLtOfToNat _ ⟨255⟩ (bits := 8) rfl

theorem mostSignificantBit_lt_256 (x : UInt256) : (mostSignificantBit x).toNat < 256 := by
  rw [mostSignificantBit, u256_lor_toNat_exact]
  exact Nat.or_lt_two_pow (n := 8) (byteAt_lt_256 _ _) (msbHigh_lt_256 x)

end Benchmarks.UniswapV4PoolManager
