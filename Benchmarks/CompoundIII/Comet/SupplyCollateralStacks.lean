import Benchmarks.CompoundIII.Comet.SupplyCollateralModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def supplyCollateralTopic : UInt256 :=
  ⟨113231870531934873813357687910685488201796133783620750046944929316499347530228⟩

def supplyCollateralWriteStack (sender dst asset : AccountAddress)
    (ptr totalPtr amount balance next ret : UInt256) (R : List UInt256) : List UInt256 :=
  [next, EVM.word dst.val, ⟨14028⟩, EVM.word asset.val, ⟨14066⟩, totalPtr, ⟨14071⟩,
    ptr, balance, ⟨14059⟩, ⟨14077⟩, EVM.word asset.val, ⟨14109⟩, supplyCollateralTopic,
    amount, EVM.word sender.val, EVM.word dst.val, ret] ++ R

def supplyCollateralMemberStack (sender dst asset : AccountAddress)
    (ptr amount balance next ret : UInt256) (R : List UInt256) : List UInt256 :=
  [ptr, balance, next, ⟨14077⟩, EVM.word asset.val, ⟨14109⟩, supplyCollateralTopic,
    amount, EVM.word sender.val, EVM.word dst.val, ret] ++ R

end Benchmarks.CompoundIII.Comet
