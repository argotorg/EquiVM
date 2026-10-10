import Benchmarks.Morpho.MetaMorphoV1_1.PermitHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.PackedWordsMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory

/-! Allocate and read the six-word permit preimage after consuming its nonce. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def permitHashPrefixMemory (mem : ByteArray) (free : Nat) (owner spender : AccountAddress)
    (value nonce : UInt256) : ByteArray :=
  wordSequenceMemory (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem) (free + 32)
    [permitTypeHash, UInt256.ofNat owner.toNat, UInt256.ofNat spender.toNat, value, nonce]

def permitHashMemory (mem : ByteArray) (free : Nat) (owner spender : AccountAddress)
    (value nonce deadline : UInt256) : ByteArray :=
  packedWordsMemory (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem) free
    (permitStructWords owner spender value nonce deadline)

theorem permitHashMemory_finish (mem : ByteArray) (free : Nat) (owner spender : AccountAddress)
    (value nonce deadline : UInt256) :
    writeWord (writeWord (writeWord (permitHashPrefixMemory mem free owner spender value nonce)
      (free + 192) deadline) free ⟨192⟩) 64 (UInt256.ofNat (free + 224)) =
      permitHashMemory mem free owner spender value nonce deadline := by
  simp only [permitHashMemory, packedWordsMemory, permitHashPrefixMemory, permitStructWords,
    wordSequenceMemory, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    Nat.add_assoc]
  rfl

theorem permitHashMemory_size (mem : ByteArray) (free : Nat) (owner spender : AccountAddress)
    (value nonce deadline : UInt256) :
    free + 224 ≤ (permitHashMemory mem free owner spender value nonce deadline).size := by
  simpa only [permitHashMemory, permitStructWords, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc] using
    packedWordsMemory_size (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem) free
      (permitStructWords owner spender value nonce deadline) (by simp [permitStructWords])

theorem permitHashMemory_free (mem : ByteArray) (free : Nat) (owner spender : AccountAddress)
    (value nonce deadline : UInt256) :
    memLoad (UInt256.ofNat 64) (permitHashMemory mem free owner spender value nonce deadline) =
      UInt256.ofNat (free + 224) := by
  simpa only [permitHashMemory, permitStructWords, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc] using
    packedWordsMemory_free (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨7⟩ mem) free
      (permitStructWords owner spender value nonce deadline)

theorem permitHashMemory_length (mem : ByteArray) (free : Nat) (owner spender : AccountAddress)
    (value nonce deadline : UInt256) (hlo : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (permitHashMemory mem free owner spender value nonce deadline) =
      ⟨192⟩ :=
  packedWordsMemory_length _ _ _ hlo hfit

theorem permitHashMemory_read (mem : ByteArray) (free : Nat) (owner spender : AccountAddress)
    (value nonce deadline : UInt256) (hlo : 96 ≤ free) :
    (permitHashMemory mem free owner spender value nonce deadline).readWithPadding
      (free + 32) 192 = wordBytes (permitStructWords owner spender value nonce deadline) :=
  packedWordsMemory_read _ _ _ hlo (by simp [permitStructWords])

end Benchmarks.Morpho.MetaMorphoV1_1
