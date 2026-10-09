import Benchmarks.Safe.SelectorWordsMemory
import Benchmarks.Safe.PostModuleSource
import Benchmarks.Safe.Blocks.Runtime_032
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def postModuleMemory (mem : ByteArray) (ptr hash : UInt256) (z : Bool) : ByteArray :=
  selectorWordPairMemory mem ptr.toNat
    (UInt256.shiftLeft (UInt256.ofNat 359013333) (UInt256.ofNat 225)) hash z.toUInt256

theorem safePostModuleMemory {mem : ByteArray} {ptr hash : UInt256} (z : Bool)
    (hf : memLoad ⟨64⟩ mem = ptr) (hb : ptr.toNat + 68 < UInt256.size) :
    safeRuntime_block_7492_taken_memory (mem := mem) (x0 := z.toUInt256) (x1 := hash) =
      postModuleMemory mem ptr hash z := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  have ha4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < UInt256.size; omega)
  have ha36 : (ptr + UInt256.ofNat 36).toNat = ptr.toNat + 36 :=
    addWord_toNat ptr ⟨36⟩ (by change ptr.toNat + 36 < UInt256.size; omega)
  simp only [safeRuntime_block_7492_taken_memory, hf, ha4, ha36,
    postModuleMemory, selectorWordPairMemory, Reasoning.Theory.writeWord]
  have hz : UInt256.isZero (UInt256.isZero z.toUInt256) = z.toUInt256 := by
    cases z <;> decide
  rw [hz]

theorem safePostModuleMemoryFree {mem : ByteArray} {ptr hash : UInt256} (z : Bool)
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (postModuleMemory mem ptr hash z) = ptr := by
  rw [postModuleMemory, selectorWordPairMemory_free _ _ _ _ _ hm hp, hf]

theorem safePostModuleEncoding (mem : ByteArray) (ptr hash : UInt256) (z : Bool) :
    config.externalABI.encode? "checkAfterModuleExecution"
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z] =
      some ((postModuleMemory mem ptr hash z).readWithPadding ptr.toNat 68) := by
  change ABI.encodeCallWithSelector? checkAfterModuleExecutionSelector
    [.elem (.bytes abiBytes32Width), .elem .bool]
    [.fixedBytes abiBytes32Width (EVM.Word.toBytesBE hash), .bool z] = _
  rw [encodeBytes32BoolCall _ _ _ (by decide), postModuleMemory,
    selectorWordPairMemory_read]
  congr 3
  decide +kernel

end Benchmarks.Safe
