import Std.Tactic.BVDecide
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.BytecodeZeroRound

/-!
# BLAKE2F-local UInt256/BitVec bridge

These lemmas are intentionally local to the Blake2f output bridge.  They expose the bytecode's
64-bit byte-swap helper as a staged `BitVec 256` expression, without adding more machinery to
`Reasoning`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def u256bv (x : UInt256) : BitVec 256 :=
  BitVec.ofNat 256 x.toNat

theorem u256bv_toNat (x : UInt256) :
    (u256bv x).toNat = x.toNat := by
  simp [u256bv, BitVec.toNat, BitVec.ofNat]
  exact x.val.isLt

theorem u256bv_inj {x y : UInt256} (h : u256bv x = u256bv y) : x = y := by
  apply u256_inj
  have hv := congrArg BitVec.toNat h
  rwa [u256bv_toNat, u256bv_toNat] at hv

theorem u256bv_land (x y : UInt256) :
    u256bv (UInt256.land x y) = u256bv x &&& u256bv y := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  simp [u256bv_toNat]
  rw [u256_land_toNat]
  change Nat.land x.toNat y.toNat % UInt256.size = Nat.land x.toNat y.toNat
  exact Nat.mod_eq_of_lt (by
    have hy : y.toNat < 2 ^ 256 := by
      change y.toNat < UInt256.size
      exact y.val.isLt
    simpa [UInt256.size] using Nat.and_lt_two_pow x.toNat hy)

theorem u256bv_lor (x y : UInt256) :
    u256bv (UInt256.lor x y) = u256bv x ||| u256bv y := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  simp [u256bv_toNat]
  rw [u256_lor_toNat]
  change Nat.lor x.toNat y.toNat % UInt256.size = Nat.lor x.toNat y.toNat
  exact Nat.mod_eq_of_lt (by
    have hx : x.toNat < 2 ^ 256 := by
      change x.toNat < UInt256.size
      exact x.val.isLt
    have hy : y.toNat < 2 ^ 256 := by
      change y.toNat < UInt256.size
      exact y.val.isLt
    simpa [UInt256.size] using Nat.or_lt_two_pow hx hy)

theorem u256bv_shl (x : UInt256) (n : Nat) (hn : n < 256) :
    u256bv (UInt256.shiftLeft x (UInt256.ofNat n)) = u256bv x <<< n := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rw [ushl_ofNat_toNat x n hn]
  simp [u256bv_toNat]
  simp [UInt256.size]

theorem u256bv_shr (x : UInt256) (n : Nat) (hn : n < 256) :
    u256bv (UInt256.shiftRight x (UInt256.ofNat n)) = u256bv x >>> n := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rw [ushr_ofNat_toNat x n hn]
  simp [u256bv_toNat]

theorem u256bv_ofNat (n : Nat) :
    u256bv (UInt256.ofNat n) = BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rfl

theorem u256bv_mk (n : Fin UInt256.size) :
    u256bv ({ val := n } : UInt256) = BitVec.ofNat 256 n.val := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  change n.val = (BitVec.ofNat 256 n.val).toNat
  rw [show (BitVec.ofNat 256 n.val).toNat = n.val % UInt256.size by rfl]
  exact (Nat.mod_eq_of_lt n.isLt).symm

def swapStep8U (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft x ⟨8⟩) ⟨18374966859414961920⟩)
    (UInt256.land (UInt256.shiftRight x ⟨8⟩) ⟨71777214294589695⟩)

def swapStep8B (x : BitVec 256) : BitVec 256 :=
  ((x <<< 8) &&& BitVec.ofNat 256 18374966859414961920) |||
  ((x >>> 8) &&& BitVec.ofNat 256 71777214294589695)

def swapStep16U (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft x ⟨16⟩) ⟨18446462603027742720⟩)
    (UInt256.land (UInt256.shiftRight x ⟨16⟩) ⟨281470681808895⟩)

def swapStep16B (x : BitVec 256) : BitVec 256 :=
  ((x <<< 16) &&& BitVec.ofNat 256 18446462603027742720) |||
  ((x >>> 16) &&& BitVec.ofNat 256 281470681808895)

def swapStep32U (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft x ⟨32⟩) ⟨18446744069414584320⟩)
    (UInt256.land (UInt256.shiftRight x ⟨32⟩) ⟨4294967295⟩)

def swapStep32B (x : BitVec 256) : BitVec 256 :=
  ((x <<< 32) &&& BitVec.ofNat 256 18446744069414584320) |||
  ((x >>> 32) &&& BitVec.ofNat 256 4294967295)

theorem u256bv_swapStep8 (x : UInt256) :
    u256bv (swapStep8U x) = swapStep8B (u256bv x) := by
  unfold swapStep8U swapStep8B
  rw [u256bv_lor, u256bv_land, u256bv_land]
  rw [show u256bv (UInt256.shiftLeft x ⟨8⟩) = u256bv x <<< 8 from by
    simpa using u256bv_shl x 8 (by decide)]
  rw [show u256bv (UInt256.shiftRight x ⟨8⟩) = u256bv x >>> 8 from by
    simpa using u256bv_shr x 8 (by decide)]
  rw [u256bv_mk, u256bv_mk, u256bv_mk]
  rfl

theorem u256bv_swapStep16 (x : UInt256) :
    u256bv (swapStep16U x) = swapStep16B (u256bv x) := by
  unfold swapStep16U swapStep16B
  rw [u256bv_lor, u256bv_land, u256bv_land]
  rw [show u256bv (UInt256.shiftLeft x ⟨16⟩) = u256bv x <<< 16 from by
    simpa using u256bv_shl x 16 (by decide)]
  rw [show u256bv (UInt256.shiftRight x ⟨16⟩) = u256bv x >>> 16 from by
    simpa using u256bv_shr x 16 (by decide)]
  rw [u256bv_mk, u256bv_mk, u256bv_mk]
  rfl

theorem u256bv_swapStep32 (x : UInt256) :
    u256bv (swapStep32U x) = swapStep32B (u256bv x) := by
  unfold swapStep32U swapStep32B
  rw [u256bv_lor, u256bv_land, u256bv_land]
  rw [show u256bv (UInt256.shiftLeft x ⟨32⟩) = u256bv x <<< 32 from by
    simpa using u256bv_shl x 32 (by decide)]
  rw [show u256bv (UInt256.shiftRight x ⟨32⟩) = u256bv x >>> 32 from by
    simpa using u256bv_shr x 32 (by decide)]
  rw [u256bv_mk, u256bv_mk, u256bv_mk]
  rfl

def bvSwap64In256 (x : BitVec 256) : BitVec 256 :=
  swapStep32B (swapStep16B (swapStep8B x))

theorem evmSwap64_eq_staged (x : UInt256) :
    evmSwap64 x = swapStep32U (swapStep16U (swapStep8U x)) := by
  rfl

theorem u256bv_evmSwap64 (x : UInt256) :
    u256bv (evmSwap64 x) = bvSwap64In256 (u256bv x) := by
  rw [evmSwap64_eq_staged]
  unfold bvSwap64In256
  rw [u256bv_swapStep32]
  rw [u256bv_swapStep16]
  rw [u256bv_swapStep8]

theorem bitvec_ofNat_shiftRight_to_extract_256 (x : BitVec 256) (k : Nat) :
    BitVec.ofNat 8 (x.toNat >>> k) = BitVec.extractLsb' k 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem bitvec_ofNat_toNat_eq_setWidth {n m : Nat} (x : BitVec n) :
    BitVec.ofNat m x.toNat = BitVec.setWidth m x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

theorem bitvec_ofNat_shiftRight_to_extract_64 (x : BitVec 64) (k : Nat) :
    BitVec.ofNat 8 (x.toNat >>> k) = BitVec.extractLsb' k 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

end Blake2f
