import Benchmarks.CurveVault.InitializeStringSource
import Benchmarks.CurveVault.InitializeStringEntries
import Benchmarks.CurveVault.RuntimeBlocks_004

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultInitializeStringWrites {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr size x2 x3 : UInt256} {R : List UInt256}
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (hsize : size.toNat ≤ 32) (hbound : mem.size ≤ 384) (hptr : ptr.toNat ≤ 352)
    (hfull : ptr.toNat + 32 ≤ mem.size) (hn : memLoad ptr mem = size)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 476) (size :: ptr :: x2 :: x3 :: R) mem aw rdata σ k C) :
    RDret fork vaultBytecode g s0
      (vaultInitializeStringAccounts I σ size (memLoad (UInt256.ofNat (ptr.toNat + 32)) mem)) ByteArray.empty := by
  let word := memLoad (UInt256.ofNat (ptr.toNat + 32)) mem
  let copied := vaultInitializeCopyMemory mem ptr
  let named := vaultInitializeNameMemory mem ptr size
  let symboled := vaultStringScratch named 2 vaultSymbolPrefix size word
  obtain ⟨hcn, hcw, _, hcsize, _⟩ := vaultInitializeCopyMemory_words mem ptr size hbound hptr hfull hn
  change 448 ≤ copied.size at hcsize
  have hnamed : named.size = copied.size := vaultStringScratch_size copied 16 vaultNamePrefix size word hcsize (by omega)
  have hnamedSize : 448 ≤ named.size := by omega
  have hframe : WordMemoryRange copied named 0 288 :=
    vaultStringScratch_frame copied 16 vaultNamePrefix size word hcsize (by omega)
  have hnn : memLoad (UInt256.ofNat 224) named = size :=
    (hframe.load 224 (by omega) (by omega) (by omega) (by decide)).trans hcn
  have hnw : memLoad (UInt256.ofNat 256) named = word :=
    (hframe.load 256 (by omega) (by omega) (by omega) (by decide)).trans hcw
  have hlen (p : Nat) (hp : p ≤ 16) : UInt256.ofNat p + size = UInt256.ofNat (size.toNat + p) := by
    apply u256_inj
    rw [uadd_toNat, ulit_toNat' p (by change p < 2 ^ 256; omega),
      ulit_toNat' (size.toNat + p) (by change size.toNat + p < 2 ^ 256; omega),
      Nat.mod_eq_of_lt (by change p + size.toNat < 2 ^ 256; omega)]
    omega
  have hheaderName : memLoad (UInt256.ofNat 352) named = UInt256.ofNat (size.toNat + 16) :=
    (vaultStringScratch_header copied 16 vaultNamePrefix size word).trans (hlen 16 (by omega))
  have hdataName : named.readWithPadding 384 64 = vaultNameData size word :=
    vaultInitializeNameMemory_payload mem ptr size hbound hptr hfull hn
  obtain ⟨aw1, k1, C1, rd598⟩ := vaultInitializeBuildName hbound hptr hfull hn hstack h
  obtain ⟨aw2, k2, C2, rd628⟩ := vaultInitializeNameLoopEntry hstack (by omega) (by omega) hheaderName rd598
  obtain ⟨aw3, k3, C3, x0', x1', rd651⟩ :=
    vaultInitializeStoreString true hperm hstack hnamedSize hheaderName hdataName rd628
  obtain ⟨aw4, k4, C4, rd768⟩ := vaultInitializeBuildSymbol hnamedSize hnn hnw hstack rd651
  rw [hlen 2 (by omega)] at rd768
  obtain ⟨aw5, k5, C5, rd786⟩ := vaultInitializeSymbolLoopEntry hstack (by omega) (by omega) rd768
  have hsymbolSize : 448 ≤ symboled.size := by
    rw [vaultStringScratch_size named 2 vaultSymbolPrefix size word hnamedSize (by omega)]
    exact hnamedSize
  have hheaderSymbol : memLoad (UInt256.ofNat 352) symboled = UInt256.ofNat (size.toNat + 2) :=
    (vaultStringScratch_header named 2 vaultSymbolPrefix size word).trans (hlen 2 (by omega))
  have hdataSymbol : symboled.readWithPadding 384 64 = vaultSymbolData size word :=
    vaultInitializeSymbolMemory_payload named size word hnamedSize hdataName
  obtain ⟨aw6, k6, C6, x0'', x1'', rd809⟩ :=
    vaultInitializeStoreString false hperm hstack hsymbolSize hheaderSymbol hdataSymbol rd786
  exact vaultBlocks.vault_block_809 (by omega) hperm rd809

end Benchmarks.CurveVault
