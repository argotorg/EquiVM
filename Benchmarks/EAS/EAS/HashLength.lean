import Benchmarks.EAS.EAS.UIDSites

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a length load followed by hashing its separately supplied data pointer.
theorem hashLength {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {pc lenPtr dataPtr : UInt256} {R : List UInt256}
    (hstack : R.length+2 ≤ 1024)
    (hd0 : decode code pc = some (.JUMPDEST,.none))
    (hd1 : decode code (pc+⟨1⟩) = some (.MLOAD,.none))
    (hd2 : decode code (pc+⟨2⟩) = some (.SWAP1,.none))
    (hd3 : decode code (pc+⟨3⟩) = some (.KECCAK256,.none))
    (rd : RD fork code ee g s0 pc (lenPtr::dataPtr::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork code ee g s0 (pc+⟨4⟩) (keccakWord dataPtr (memLoad lenPtr mem) mem::R) mem aw' rdata σ k' C' := by
  have rd1 := RD.jumpdest rd hd0 (by simp only [List.length_cons]; omega)
  have rd2 := RD.genMload rd1 hd1 (by simp only [List.length_cons]; omega)
  have rd3 := RD.swap1 rd2 (by simpa only [u256_add_assoc,show (⟨1⟩ : UInt256)+⟨1⟩=⟨2⟩ from rfl] using hd2) hstack
  have rd4 := RD.genKeccak256 rd3 (by simpa only [u256_add_assoc,
    show (⟨1⟩ : UInt256)+(⟨1⟩+⟨1⟩)=⟨3⟩ from rfl] using hd3) (by omega)
  obtain ⟨k',C',hr⟩ := RD.pack rd4
  simp only [u256_add_assoc,show (⟨1⟩ : UInt256)+(⟨1⟩+(⟨1⟩+⟨1⟩))=⟨4⟩ from rfl] at hr
  exact ⟨_,k',C',hr⟩

end Benchmarks.EAS.EAS
