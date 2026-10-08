import Benchmarks.CompoundIII.Comet.PackedWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def initializeTimeWord (old time : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft time (UInt256.ofNat 208))
      (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208)))
    (UInt256.land old
      (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208))))

def initializeIndicesWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.ofNat 18446744073709551617000000000000000)
    (UInt256.land
      (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1))) old)

theorem initializeTimeWord_packed (old time : UInt256) :
    packedWriteWord old time 26 5 = initializeTimeWord old time := by
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨time.val⟩
  rw [packedWriteWord_bitvec x y 26 5 (by decide) (by decide) (by decide)]
  have hb : x % BitVec.ofNat 256 (256^26) +
      BitVec.ofNat 256 (256^26) * (y % BitVec.ofNat 256 (256^5)) +
      BitVec.ofNat 256 (256^31) * (x / BitVec.ofNat 256 (256^31)) =
      ((y <<< 208) &&& BitVec.ofNat 256 ((2^40-1)*2^208)) |||
        (x &&& BitVec.ofNat 256 (2^256-1-(2^40-1)*2^208)) := by bv_decide
  rw [hb]
  simp only [initializeTimeWord, UInt256.land, UInt256.lor, BitVec.toFin_and, BitVec.toFin_or]
  rfl

theorem initializeIndexBits (x : BitVec 256) :
    let y := BitVec.ofNat 256 1000000000000000
    let a := x % BitVec.ofNat 256 (256^0) +
      BitVec.ofNat 256 (256^0) * (y % BitVec.ofNat 256 (256^8)) +
      BitVec.ofNat 256 (256^8) * (x / BitVec.ofNat 256 (256^8))
    a % BitVec.ofNat 256 (256^8) +
      BitVec.ofNat 256 (256^8) * (y % BitVec.ofNat 256 (256^8)) +
      BitVec.ofNat 256 (256^16) * (a / BitVec.ofNat 256 (256^16)) =
      BitVec.ofNat 256 18446744073709551617000000000000000 |||
        (BitVec.ofNat 256 (2^256-2^128) &&& x) := by
  dsimp only
  bv_decide

theorem initializeIndicesWord_packed (old : UInt256) :
    packedWriteWord (packedWriteWord old ⟨1000000000000000⟩ 0 8)
      ⟨1000000000000000⟩ 8 8 = initializeIndicesWord old := by
  let x : BitVec 256 := ⟨old.val⟩
  let y := BitVec.ofNat 256 1000000000000000
  change packedWriteWord (packedWriteWord ⟨x.toFin⟩ ⟨y.toFin⟩ 0 8) ⟨y.toFin⟩ 8 8 = _
  have h1 := packedWriteWord_bitvec x y 0 8 (by decide) (by decide) (by decide)
  rw [h1, packedWriteWord_bitvec _ y 8 8 (by decide) (by decide) (by decide)]
  have hb := initializeIndexBits x
  rw [hb]
  simp only [initializeIndicesWord, UInt256.land, UInt256.lor, BitVec.toFin_and, BitVec.toFin_or]
  rfl

end Benchmarks.CompoundIII.Comet
