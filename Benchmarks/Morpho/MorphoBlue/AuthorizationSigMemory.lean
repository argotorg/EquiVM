import Benchmarks.Morpho.MorphoBlue.AuthorizationSigDecode
import Benchmarks.Morpho.MorphoBlue.WordBufferLoad
import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def AuthorizationWords.toList (a : AuthorizationWords) : List UInt256 :=
  [a.authorizer, a.authorized, a.enabled, a.nonce, a.deadline]

def AuthorizationWords.InMemory (a : AuthorizationWords) (mem : ByteArray) : Prop :=
  ∀ i : Fin 5, memLoad (UInt256.ofNat (128 + 32 * i.val)) mem = a.toList[i]

theorem authorizationDecodedMem_size (a : AuthorizationWords) :
    (authorizationDecodedMem a).size = 288 := by
  have hs : (writeWord solcFreePtrMem 64 (UInt256.ofNat 288)).size = 96 := by native_decide
  rw [authorizationDecodedMem, writeReturnWords_size _ _ _ (by simp)
    (by rw [hs]; exact lt_usize _ (by decide)), hs]
  rfl

theorem authorizationDecodedMem_free (a : AuthorizationWords) :
    memLoad (UInt256.ofNat 64) (authorizationDecodedMem a) = UInt256.ofNat 288 := by
  have hs : (writeWord solcFreePtrMem 64 (UInt256.ofNat 288)).size = 96 := by native_decide
  rw [authorizationDecodedMem, memLoad_writeReturnWords_below _ _ _ _
    (by rw [hs]; exact lt_usize _ (by decide)) (by rw [hs]; decide) (by decide)]
  native_decide

theorem authorizationDecodedMem_loads (a : AuthorizationWords) :
    a.InMemory (authorizationDecodedMem a) := by
  have hs : (writeWord solcFreePtrMem 64 (UInt256.ofNat 288)).size = 96 := by native_decide
  intro i
  exact memLoad_writeReturnWords a.toList _ 128 i
    (by rw [hs]; exact lt_usize _ (by decide)) (by change 288 < UInt256.size; decide)

theorem AuthorizationWords.InMemory.prefix {a : AuthorizationWords} {before after : ByteArray}
    {limit : Nat} (ha : a.InMemory before) (hp : MemoryPrefix before after limit)
    (hl : 288 ≤ limit) (hs : 288 ≤ before.size) : a.InMemory after := by
  intro i
  have hi := i.isLt
  rw [memoryPrefix_memLoad hp _
    (by rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]; omega)]
  exact ha i

theorem AuthorizationWords.InMemory.hash {a : AuthorizationWords} {mem : ByteArray}
    (ha : a.InMemory mem) (hs : 288 ≤ mem.size) (key slot : UInt256) :
    a.InMemory (twoWordHashMem key slot mem) := by
  intro i
  have hi := i.isLt
  rw [twoWordHashMem_memLoad_above64 _ _ _
    (by rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]; omega)]
  exact ha i

theorem AuthorizationWords.InMemory.message {a : AuthorizationWords} {mem : ByteArray}
    {free : Nat} (ha : a.InMemory mem) (hs : mem.size = free)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hl : 288 ≤ free) (hh : free + 64 < 2 ^ 64) (len payload : UInt256) :
    a.InMemory (morphoErrorMem len payload mem) := by
  have hu : free < UInt256.size := by change _ < 2 ^ 256; omega
  have hp := morphoErrorMem_prefix len payload (by omega : 96 ≤ mem.size) hf
    (by rw [UInt256.toNat_ofNat_of_lt hu, hs]; simpa only [Nat.sub_self] using USize.size_pos)
    (by rw [UInt256.toNat_ofNat_of_lt hu]; change _ < 2 ^ 256; omega)
  exact ha.prefix hp (by rw [UInt256.toNat_ofNat_of_lt hu]; exact hl) (by omega)

def authorizationExpiredWord : UInt256 :=
  UInt256.ofNat 52202210384608418486011761823268687924597144129027754648567040468564079280128

def authorizationExpiredMem (a : AuthorizationWords) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 17) authorizationExpiredWord (authorizationDecodedMem a)

theorem authorizationExpiredMem_properties (a : AuthorizationWords) :
    (authorizationExpiredMem a).size = 352 ∧
      memLoad (UInt256.ofNat 64) (authorizationExpiredMem a) = UInt256.ofNat 352 ∧
      a.InMemory (authorizationExpiredMem a) ∧
      morphoErrorLength (authorizationExpiredMem a) (UInt256.ofNat 288) = UInt256.ofNat 17 := by
  have hs := authorizationDecodedMem_size a
  have hf := authorizationDecodedMem_free a
  have hp := morphoErrorMem_properties (UInt256.ofNat 17) authorizationExpiredWord
    (UInt256.ofNat 288) (authorizationDecodedMem a) (by exact hs) hf (by decide) (by decide)
  exact ⟨hp.1, hp.2.1, (authorizationDecodedMem_loads a).message hs hf
    (by decide) (by decide) _ _, hp.2.2⟩

end Benchmarks.Morpho.MorphoBlue
