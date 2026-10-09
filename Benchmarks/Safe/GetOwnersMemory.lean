import Benchmarks.Safe.AddressArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def getOwnersStepMemory (mem : ByteArray) (i : Nat) (current : UInt256) : ByteArray :=
  twoWordHashMem current ⟨2⟩ (writeWord mem (160 + 32 * i) current)

theorem AddressArrayMemory.step {mem n words} (h : AddressArrayMemory mem n words)
    (i : Nat) (current : UInt256) (hi : i < n) :
    AddressArrayMemory (getOwnersStepMemory mem i current) n (words.set i current) :=
  (h.write i current hi).scratch current ⟨2⟩

end Benchmarks.Safe
