import Benchmarks.Morpho.MetaMorphoV1_1.StringReturnRoutines

/-! Successful allocation and return of a copied storage string. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem stringAllocatedReturn {g : Sat256} {s0 evm : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (base : UInt256)
    (hstack : R.length + 13 ≤ 1024)
    (hvalid : storageStringValid (storageStringHeader evm base))
    (hfit : allocationFits ⟨128⟩
      (stringCopySize (storageStringLength (storageStringHeader evm base))))
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨11329⟩
      (stringAllocationStack (storageStringLength (storageStringHeader evm base)) R)
      (stringCopyMemory evm.executionEnv evm.accountMap mem base (storageStringHeader evm base)
        (storageStringLength (storageStringHeader evm base))) aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 evm.accountMap
      (stringReturnBytes (storageStringBytes evm base)) := by
  let len := storageStringLength (storageStringHeader evm base)
  let copied := stringCopyMemory evm.executionEnv evm.accountMap mem base
    (storageStringHeader evm base) len
  have hlen : len.toNat < 2 ^ 255 := storageStringLength_lt _
  have hcopy : 160 + 32 * stringWordCount len ≤ copied.size :=
    stringCopyMemory_size _ _ _ _ _ hvalid
  have hcover : len.toNat ≤ 32 * stringWordCount len := by unfold stringWordCount; omega
  have hfree64 : 160 + 32 * stringWordCount len < 2 ^ 64 := by
    have h := hfit.1
    rw [stringCopyNextCursor _ hlen, stringCopyEnd_toNat _ hlen] at h
    exact h
  obtain ⟨aw1, k1, C1, h1⟩ := allocateRoundedReturn v
    (by change R.length + 11 ≤ 1024; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  rw [stringCopyNextCursor _ hlen] at h1
  have hm : 160 + len.toNat ≤
      (Reasoning.Theory.writeWord copied 64 (stringCopyEnd len)).size := by
    rw [writeWord_sparse_size]
    omega
  have hptr : memLoad (UInt256.ofNat 64)
      (Reasoning.Theory.writeWord copied 64 (stringCopyEnd len)) =
      UInt256.ofNat (160 + 32 * stringWordCount len) :=
    memLoad_write_same _ _ _ _ rfl
  have hl : memLoad ⟨128⟩ (Reasoning.Theory.writeWord copied 64 (stringCopyEnd len)) = len := by
    rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by change 160 ≤ copied.size; omega) (.inr (by decide))]
    exact stringCopyMemory_length _ _ _ _ _ _
  have hb : (Reasoning.Theory.writeWord copied 64 (stringCopyEnd len)).readWithPadding
      160 len.toNat = storageStringBytes evm base := by
    rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _ (by omega) (.inr (by decide))]
    exact stringCopyMemory_read _ _ _ hvalid
  exact stringReturnRoutine v len (storageStringBytes evm base)
    (160 + 32 * stringWordCount len)
    (by change R.length + 13 ≤ 1024; exact hstack) hlen
    (by omega) (by
      change 160 + 32 * stringWordCount len + 64 + 32 * stringWordCount len + 32 < 2 ^ 256
      omega) hm hptr hl (storageStringBytes_size _ _) hb h1

end Benchmarks.Morpho.MetaMorphoV1_1
