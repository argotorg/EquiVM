import Benchmarks.Morpho.MorphoBlue.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

def wad : UInt256 := UInt256.ofNat 1000000000000000000

def taylorTerm1 (x n : UInt256) : UInt256 := UInt256.mul x n

def taylorTerm2 (x n : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul (taylorTerm1 x n) (taylorTerm1 x n))
    (UInt256.ofNat 2000000000000000000)

def taylorTerm3 (x n : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul (taylorTerm2 x n) (taylorTerm1 x n))
    (UInt256.ofNat 3000000000000000000)

def TaylorFits (x n : UInt256) : Prop :=
  x.toNat * n.toNat < UInt256.size ∧
  (taylorTerm1 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size ∧
  (taylorTerm2 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size ∧
  (taylorTerm1 x n).toNat + (taylorTerm2 x n).toNat < UInt256.size ∧
  (taylorTerm1 x n + taylorTerm2 x n).toNat + (taylorTerm3 x n).toNat < UInt256.size

def taylorWord (x n : UInt256) : UInt256 :=
  (taylorTerm1 x n + taylorTerm2 x n) + taylorTerm3 x n

end Benchmarks.Morpho.MorphoBlue
