import Benchmarks.CurveVault.InitializeNameMemory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultSymbolPrefix : UInt256 :=
  UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512

def vaultSymbolData (size word : UInt256) : ByteArray :=
  vaultSymbolPrefix.toByteArray.extract 0 2 ++ word.toByteArray ++
    word.toByteArray.extract 18 32 ++ size.toByteArray.extract 16 32

theorem vaultInitializeSymbolMemory_block (mem : ByteArray) (size word : UInt256) (R : List UInt256)
    (hmem : 448 ≤ mem.size) (hn : memLoad (UInt256.ofNat 224) mem = size)
    (hw : memLoad (UInt256.ofNat 256) mem = word) :
    vaultBlocks.vault_block_651_memory (mem := mem) = vaultStringScratch mem 2 vaultSymbolPrefix size word ∧
    vaultBlocks.vault_block_651_stack (mem := mem) (R := R) =
      (UInt256.ofNat 31 + ((UInt256.ofNat 2 + size) + UInt256.ofNat 32)) :: ⟨0⟩ ::
        ((UInt256.ofNat 2 + size) + UInt256.ofNat 32) :: UInt256.ofNat 352 :: R := by
  let prepared := vaultStringPrepared mem 2 vaultSymbolPrefix
  let staged := vaultStringStaged mem 2 vaultSymbolPrefix
  obtain ⟨h2, hpre, hsn, hsw⟩ := vaultStringScratch_inputs mem 2 vaultSymbolPrefix size word hmem hn hw
  have hm : vaultBlocks.vault_block_651_memory (mem := mem) = vaultStringScratch mem 2 vaultSymbolPrefix size word := by
    change writeWord
      (writeWord (writeWord prepared 384 (memLoad (UInt256.ofNat 320) prepared))
        (UInt256.ofNat 384 + (⟨0⟩ + memLoad (UInt256.ofNat 288) prepared)).toNat
        (memLoad (UInt256.ofNat 256) (writeWord prepared 384 (memLoad (UInt256.ofNat 320) prepared))))
      352 ((⟨0⟩ + memLoad (UInt256.ofNat 288) prepared) +
        memLoad (UInt256.ofNat 224) (writeWord prepared 384 (memLoad (UInt256.ofNat 320) prepared))) = _
    rw [h2, hpre]
    change writeWord (writeWord staged 386 (memLoad (UInt256.ofNat 256) staged)) 352
      (UInt256.ofNat 2 + memLoad (UInt256.ofNat 224) staged) = _
    rw [hsn, hsw]
    rfl
  refine ⟨hm, ?_⟩
  change ((UInt256.ofNat 31 + (memLoad (UInt256.ofNat 352) (vaultBlocks.vault_block_651_memory (mem := mem)) + UInt256.ofNat 32)) ::
    ⟨0⟩ :: (memLoad (UInt256.ofNat 352) (vaultBlocks.vault_block_651_memory (mem := mem)) + UInt256.ofNat 32) ::
      UInt256.ofNat 352 :: R) = _
  rw [hm, vaultStringScratch_header]

theorem vaultNameData_tail (size word : UInt256) :
    (vaultNameData size word).extract 34 64 =
      word.toByteArray.extract 18 32 ++ size.toByteArray.extract 16 32 := by
  have hpre : (vaultNamePrefix.toByteArray.extract 0 16).size = 16 := by
    rw [ByteArray.size_extract, toByteArray_size]; rfl
  have hcore : (vaultNamePrefix.toByteArray.extract 0 16 ++ word.toByteArray).size = 48 := by
    rw [ByteArray.size_append, hpre, toByteArray_size]
  have htail : (size.toByteArray.extract 16 32).size = 16 := by
    rw [ByteArray.size_extract, toByteArray_size]; rfl
  unfold vaultNameData
  rw [extract_append_span _ _ _ _ (by rw [hcore]; omega) (by rw [hcore]; omega), hcore,
    extract_append_right_window _ _ _ _ (by rw [hpre]; omega), hpre]
  have hlast : (size.toByteArray.extract 16 32).extract 0 16 = size.toByteArray.extract 16 32 := by
    simpa only [htail] using byteArray_extract_self (size.toByteArray.extract 16 32)
  change word.toByteArray.extract 18 32 ++ (size.toByteArray.extract 16 32).extract 0 16 = _
  rw [hlast]

theorem vaultInitializeSymbolMemory_payload (mem : ByteArray) (size word : UInt256)
    (hmem : 448 ≤ mem.size) (hname : mem.readWithPadding 384 64 = vaultNameData size word) :
    (vaultStringScratch mem 2 vaultSymbolPrefix size word).readWithPadding 384 64 = vaultSymbolData size word := by
  rw [vaultStringScratch_payload _ _ _ _ _ hmem (by omega) (by omega)]
  have htail : mem.readWithPadding 418 30 = word.toByteArray.extract 18 32 ++ size.toByteArray.extract 16 32 := by
    rw [readWithPadding_eq_extract_unbounded mem 418 30 (by omega) (by omega)]
    have hname' : mem.extract 384 448 = vaultNameData size word := by
      rw [← readWithPadding_eq_extract_unbounded mem 384 64 (by omega) hmem]
      exact hname
    have hslice : (mem.extract 384 448).extract 34 64 = mem.extract 418 448 := by
      rw [extract_extract_BA]; rfl
    rw [← hslice, hname', vaultNameData_tail]
  change vaultSymbolPrefix.toByteArray.extract 0 2 ++ word.toByteArray ++ mem.readWithPadding 418 30 = _
  rw [htail]
  exact ByteArray.append_assoc.symm

theorem vaultInitializeBuildSymbol {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {size word x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hmem : 448 ≤ mem.size) (hn : memLoad (UInt256.ofNat 224) mem = size)
    (hw : memLoad (UInt256.ofNat 256) mem = word) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 651) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 768)
      ((UInt256.ofNat 31 + ((UInt256.ofNat 2 + size) + UInt256.ofNat 32)) :: ⟨0⟩ ::
        ((UInt256.ofNat 2 + size) + UInt256.ofNat 32) :: UInt256.ofNat 352 :: R)
      (vaultStringScratch mem 2 vaultSymbolPrefix size word) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_651_packed hstack h
  obtain ⟨hm, hstk⟩ := vaultInitializeSymbolMemory_block mem size word R hmem hn hw
  rw [hm, hstk] at rd
  exact ⟨aw', k', C', rd⟩

end Benchmarks.CurveVault
