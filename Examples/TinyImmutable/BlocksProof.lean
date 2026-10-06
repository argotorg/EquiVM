import Examples.TinyImmutable.Common
import Examples.TinyImmutable.BlocksAuto

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables

namespace TinyImmutable

/-- The shared runtime dispatcher prefix, proved from the generated block summaries. -/
theorem tinyBlocksReachSelector {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD (patchedRuntime v) I g (initState σ σ₀ g A I) ⟨25⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have hvalid15 : (D_J (immutableLayout.runtime tinyImmutableBytecode (immutableWords v)) 0).contains
      (UInt256.ofNat 15) = true := by
    exact tinyContains15 v
  have rd15 := tinyImmutableBlocks.tinyImmutable_block_0_taken
    (immWords := immutableWords v) (by decide) (by rw [hwv]; decide) hvalid15 rd0
  have rd25 := tinyImmutableBlocks.tinyImmutable_block_15_fallthrough
    (immWords := immutableWords v) (by decide)
    (lt_four_eq_zero_of_ge hsz hsize) rd15
  exact ⟨_, _, by
    simpa [tinyImmutableBlocks.tinyImmutable_block_0_taken_stack,
      tinyImmutableBlocks.tinyImmutable_block_0_taken_memory,
      tinyImmutableBlocks.tinyImmutable_block_15_fallthrough_stack,
      solcFreePtrMem, patchedRuntime] using rd25⟩

theorem tinyBlocksReachOwnerBody {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState σ σ₀ g A I) ⟨67⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd25⟩ := tinyBlocksReachSelector v hcode hwv hsz hsize
  have hvalid : (D_J (immutableLayout.runtime tinyImmutableBytecode (immutableWords v)) 0).contains
      (UInt256.ofNat 67) = true := by
    exact tinyContains67 v
  have hcond : UInt256.eq ⟨2376452955⟩ (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [solcSelectorWord, tinyOwnerEvmSelector hsz, howner]
    decide
  have h := tinyImmutableBlocks.tinyImmutable_block_25_taken (immWords := immutableWords v)
    (by decide) (by simpa [solcSelectorWord] using hcond) hvalid rd25
  exact ⟨_, _, by
    simpa [tinyImmutableBlocks.tinyImmutable_block_25_taken_stack,
      solcSelectorWord, patchedRuntime] using h⟩

theorem tinyBlocksReachQuoteBody {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState σ σ₀ g A I) ⟨148⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd25⟩ := tinyBlocksReachSelector v hcode hwv hsz hsize
  have hownerCond : UInt256.eq ⟨2376452955⟩ (solcSelectorWord I) = ⟨0⟩ := by
    rw [solcSelectorWord, tinyOwnerEvmSelector hsz, howner]
    decide
  have rd41 := tinyImmutableBlocks.tinyImmutable_block_25_fallthrough
    (immWords := immutableWords v) (by decide)
    (by simpa [solcSelectorWord] using hownerCond) rd25
  have hquoteCond : UInt256.eq ⟨3978024812⟩ (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [solcSelectorWord, tinyQuoteEvmSelector hsz, hquote]
    decide
  have hvalid : (D_J (immutableLayout.runtime tinyImmutableBytecode (immutableWords v)) 0).contains
      (UInt256.ofNat 148) = true := by
    exact tinyContains148 v
  have h := tinyImmutableBlocks.tinyImmutable_block_41_taken (immWords := immutableWords v)
    (by decide) (by simpa [solcSelectorWord] using hquoteCond) hvalid rd41
  exact ⟨_, _, by
    simpa [tinyImmutableBlocks.tinyImmutable_block_25_fallthrough_stack,
      solcSelectorWord, patchedRuntime] using h⟩

theorem tinyBlocksReachScaleBody {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = false)
    (hscale : (scaleSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState σ σ₀ g A I) ⟨181⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd25⟩ := tinyBlocksReachSelector v hcode hwv hsz hsize
  have hownerCond : UInt256.eq ⟨2376452955⟩ (solcSelectorWord I) = ⟨0⟩ := by
    rw [solcSelectorWord, tinyOwnerEvmSelector hsz, howner]
    decide
  have rd41 := tinyImmutableBlocks.tinyImmutable_block_25_fallthrough
    (immWords := immutableWords v) (by decide)
    (by simpa [solcSelectorWord] using hownerCond) rd25
  have hquoteCond : UInt256.eq ⟨3978024812⟩ (solcSelectorWord I) = ⟨0⟩ := by
    rw [solcSelectorWord, tinyQuoteEvmSelector hsz, hquote]
    decide
  have rd52 := tinyImmutableBlocks.tinyImmutable_block_41_fallthrough
    (immWords := immutableWords v) (by decide)
    (by simpa [tinyImmutableBlocks.tinyImmutable_block_25_fallthrough_stack,
      solcSelectorWord] using hquoteCond) rd41
  have hscaleCond : UInt256.eq ⟨4112390170⟩ (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [solcSelectorWord, tinyScaleEvmSelector hsz, hscale]
    decide
  have hvalid : (D_J (immutableLayout.runtime tinyImmutableBytecode (immutableWords v)) 0).contains
      (UInt256.ofNat 181) = true := by
    exact tinyContains181 v
  have h := tinyImmutableBlocks.tinyImmutable_block_52_taken (immWords := immutableWords v)
    (by decide) (by simpa [tinyImmutableBlocks.tinyImmutable_block_25_fallthrough_stack,
      solcSelectorWord] using hscaleCond) hvalid rd52
  exact ⟨_, _, by
    simpa [tinyImmutableBlocks.tinyImmutable_block_25_fallthrough_stack,
      solcSelectorWord, patchedRuntime] using h⟩

theorem tinyBlocksX_callvalue_ne {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (patchedRuntime v) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd12 := tinyImmutableBlocks.tinyImmutable_block_0_fallthrough
    (immWords := immutableWords v) (by decide) (isZero_eq_zero_of_ne hwv) rd0
  have hrev := tinyImmutableBlocks.tinyImmutable_block_12 (immWords := immutableWords v)
    (by simp [tinyImmutableBlocks.tinyImmutable_block_0_fallthrough_stack]) rd12
  simpa using hrev

theorem tinyBlocksX_short {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev (patchedRuntime v) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have hvalid15 : (D_J (immutableLayout.runtime tinyImmutableBytecode (immutableWords v)) 0).contains
      (UInt256.ofNat 15) = true := by
    exact tinyContains15 v
  have rd15 := tinyImmutableBlocks.tinyImmutable_block_0_taken
    (immWords := immutableWords v) (by decide) (by rw [hwv]; decide) hvalid15 rd0
  have hvalid63 : (D_J (immutableLayout.runtime tinyImmutableBytecode (immutableWords v)) 0).contains
      (UInt256.ofNat 63) = true := by
    exact tinyContains63 v
  have rd63 := tinyImmutableBlocks.tinyImmutable_block_15_taken
    (immWords := immutableWords v) (by decide) (lt_four_ne_zero_of_lt hsz) hvalid63 rd15
  have hrev := tinyImmutableBlocks.tinyImmutable_block_63 (immWords := immutableWords v)
    (by simp [tinyImmutableBlocks.tinyImmutable_block_15_taken_stack]) rd63
  simpa using hrev

theorem tinyBlocksX_noMatch {σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = false)
    (hscale : (scaleSelBytes == I.calldata.extract 0 4) = false) :
    RDrev (patchedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd25⟩ := tinyBlocksReachSelector v hcode hwv hsz hsize
  have hownerCond : UInt256.eq ⟨2376452955⟩ (solcSelectorWord I) = ⟨0⟩ := by
    rw [solcSelectorWord, tinyOwnerEvmSelector hsz, howner]
    decide
  have rd41 := tinyImmutableBlocks.tinyImmutable_block_25_fallthrough
    (immWords := immutableWords v) (by decide)
    (by simpa [solcSelectorWord] using hownerCond) rd25
  have hquoteCond : UInt256.eq ⟨3978024812⟩ (solcSelectorWord I) = ⟨0⟩ := by
    rw [solcSelectorWord, tinyQuoteEvmSelector hsz, hquote]
    decide
  have rd52 := tinyImmutableBlocks.tinyImmutable_block_41_fallthrough
    (immWords := immutableWords v) (by decide)
    (by simpa [tinyImmutableBlocks.tinyImmutable_block_25_fallthrough_stack,
      solcSelectorWord] using hquoteCond) rd41
  have hscaleCond : UInt256.eq ⟨4112390170⟩ (solcSelectorWord I) = ⟨0⟩ := by
    rw [solcSelectorWord, tinyScaleEvmSelector hsz, hscale]
    decide
  have rd63 := tinyImmutableBlocks.tinyImmutable_block_52_fallthrough
    (immWords := immutableWords v) (by decide)
    (by simpa [tinyImmutableBlocks.tinyImmutable_block_25_fallthrough_stack,
      solcSelectorWord] using hscaleCond) rd52
  have hrev := tinyImmutableBlocks.tinyImmutable_block_63 (immWords := immutableWords v)
    (by simp) rd63
  simpa using hrev

theorem RD.tinyBlocksReturnWord167 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : TinyImmutables} {val : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (patchedRuntime v) ee g s0 ⟨167⟩ (val :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret (patchedRuntime v) g s0 acc (UInt256.toByteArray val) := by
  have hvalid : (D_J (immutableLayout.runtime tinyImmutableBytecode (immutableWords v)) 0).contains
      (UInt256.ofNat 139) = true := by
    exact tinyContains139 v
  have rd139 := tinyImmutableBlocks.tinyImmutable_block_167 (immWords := immutableWords v)
    (by omega) hvalid h
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  have hmem : tinyImmutableBlocks.tinyImmutable_block_167_memory
      (mem := solcFreePtrMem) (x0 := val) = solcReturnMem val := by
    simp [tinyImmutableBlocks.tinyImmutable_block_167_memory, hload, solcReturnMem,
      show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  rw [hmem] at rd139
  have hret := tinyImmutableBlocks.tinyImmutable_block_139 (immWords := immutableWords v)
    (by omega) rd139
  have hloadRet : memLoad (UInt256.ofNat 64) (solcReturnMem val) = ⟨128⟩ := by
    simpa [memLoad] using solcReturnMem_mload64 val
  rw [hloadRet] at hret
  simpa [tinyImmutableBlocks.tinyImmutable_block_167_stack, hload,
    show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (UInt256.sub (UInt256.ofNat 32 + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
    solcReturnMem_read128, patchedRuntime] using hret

theorem RD.tinyBlocksReturnAddress106 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : TinyImmutables} {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (patchedRuntime v) ee g s0 ⟨106⟩ (val :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret (patchedRuntime v) g s0 acc
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  have rd139 := tinyImmutableBlocks.tinyImmutable_block_106 (immWords := immutableWords v)
    (by simp only [List.length_cons] at hov ⊢; omega) h
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  have hmem : tinyImmutableBlocks.tinyImmutable_block_106_memory
      (mem := solcFreePtrMem) (x0 := val) =
      solcReturnMem (UInt256.land val solcAddrMask) := by
    have hmask : UInt256.ofNat 1461501637330902918203684832716283019655932542975 =
        solcAddrMask := by native_decide
    simp [tinyImmutableBlocks.tinyImmutable_block_106_memory, hload,
      solcReturnMem, hmask,
      show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  rw [hmem] at rd139
  have hret := tinyImmutableBlocks.tinyImmutable_block_139 (immWords := immutableWords v)
    (by simp only [List.length_cons] at hov ⊢; omega) rd139
  have hloadRet : memLoad (UInt256.ofNat 64)
      (solcReturnMem (UInt256.land val solcAddrMask)) = ⟨128⟩ := by
    simpa [memLoad] using solcReturnMem_mload64 (UInt256.land val solcAddrMask)
  rw [hloadRet] at hret
  simpa [tinyImmutableBlocks.tinyImmutable_block_106_stack, hload,
    show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (UInt256.sub (UInt256.ofNat 32 + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
    solcReturnMem_read128, patchedRuntime] using hret

end TinyImmutable
