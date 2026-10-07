import Benchmarks.Dss.Cat.Common
import Benchmarks.Dss.Cat.BiteEVM
import Benchmarks.Dss.Cat.BiteWalk
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

theorem catBiteBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I :=
  catBiteBodyImpl hcode hsize hwv hsel

end Benchmarks.Dss.Cat
