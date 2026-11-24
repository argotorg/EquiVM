import Benchmarks.CurveVault.ConversionPrefix
import Benchmarks.CurveVault.RuntimeBlocks_027

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault



def vaultConversionPrefixOutcome (fork : Ethereum.Fork) (s0 evm : State) (I : ExecutionEnv) (g : Sat256)
    (locals : Store) (mem : ByteArray) (next : UInt256) (R : List UInt256) : Prop :=
  (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (mem' : ByteArray)
      (total aw' : UInt256) (out : ByteArray) (k' C' : Nat),
    ExecBlock fork config {contract := contract, locals := locals} evm vaultConversionPrefix
      (.ok {contract := contract, locals := locals'} evm') ∧
    SourceState s0 I σ' evm' ∧
    locals'.get? "total_assets" = some (.int (Int.ofNat total.toNat)) ∧
    (∀ name, name ≠ "total_assets" → name ≠ "__c0" → locals'.get? name = locals.get? name) ∧
    WordMemoryRange mem mem' 224 416 ∧ WordMemoryRange mem mem' 480 UInt256.size ∧
    448 ≤ mem'.size ∧ memLoad (UInt256.ofNat 416) mem' = total ∧
    RD fork vaultBytecode I g s0 next R mem' aw' out σ' k' C') ∨
  (ExecBlock fork config {contract := contract, locals := locals} evm vaultConversionPrefix .reverted ∧
    RDrev fork vaultBytecode g s0)

theorem vaultConversionPrepare {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {pc next returnPc total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm)
    (harg : locals.get? "_total_assets" = some (.int (Int.ofNat total.toNat)))
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (hprovided : total ≠ vaultMaxWord →
      RD fork vaultBytecode I g s0 pc R mem aw rdata σ k C →
      ∃ aw' k' C', RD fork vaultBytecode I g s0 next R
        (total.toByteArray.write 0 mem 416 32) aw' rdata σ k' C')
    (hcomputed : total = vaultMaxWord →
      RD fork vaultBytecode I g s0 pc R mem aw rdata σ k C →
      ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 6772)
        (UInt256.ofNat 448 :: returnPc :: R) (total.toByteArray.write 0 mem 416 32) aw' rdata σ k' C')
    (hresume : ∀ {mem' aw' out σ' k' C'},
      RD fork vaultBytecode I g s0 returnPc R mem' aw' out σ' k' C' →
      ∃ aw'' k'' C'', RD fork vaultBytecode I g s0 next R
        ((memLoad (UInt256.ofNat 448) mem').toByteArray.write 0 mem' 416 32) aw'' out σ' k'' C'')
    (h : RD fork vaultBytecode I g s0 pc R mem aw rdata σ k C) :
    vaultConversionPrefixOutcome fork s0 evm I g locals mem next R := by
  let preMem := total.toByteArray.write 0 mem 416 32
  have preSize : 448 ≤ preMem.size := toByteArray_write_size_ge_off_add32 _ _ 416
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num)))
  have preLow : WordMemoryRange mem preMem 224 416 :=
    wordMemoryRange_write mem total 416 224 416
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num))) (Or.inl (by omega))
  have preHigh : WordMemoryRange mem preMem 480 UInt256.size :=
    wordMemoryRange_write mem total 416 480 UInt256.size
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num))) (Or.inr (by omega))
  by_cases hmax : total = vaultMaxWord
  · obtain ⟨aw0, k0, C0, rdCall⟩ := hcomputed hmax h
    rcases vaultTotalAssetsRoutine hs hstack hvalid rdCall with hsuccess | ⟨hbody, hrev⟩
    · rcases hsuccess with ⟨evm', σ', calleeLocals, a, b, c, aw1, out, k1, C1, hbody, hs', rdResume⟩
      let value := UInt256.sub (a + b) c
      let scratch := vaultTotalAssetsScratch preMem a b c
      let returned := value.toByteArray.write 0 scratch 448 32
      have hvalue : memLoad (UInt256.ofNat 448) returned = value :=
        memLoad_write_back _ _ 448 (by decide +kernel)
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num)))
      obtain ⟨aw2, k2, C2, rdNext⟩ := hresume rdResume
      change RD fork vaultBytecode I g s0 next R
        ((memLoad (UInt256.ofNat 448) returned).toByteArray.write 0 returned 416 32) aw2 out σ' k2 C2 at rdNext
      rw [hvalue] at rdNext
      have frameScratch : WordMemoryRange preMem scratch 224 UInt256.size := by
        have hf := vaultTotalAssetsScratch_frame preMem a b c (by omega)
        exact ⟨Nat.le_of_eq hf.1.symm, fun off hlo _ hin hoff => hf.2 off hlo hin hoff⟩
      have returnLow : WordMemoryRange scratch returned 224 416 :=
        wordMemoryRange_write _ _ 448 224 416
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))) (Or.inl (by omega))
      have returnHigh : WordMemoryRange scratch returned 480 UInt256.size :=
        wordMemoryRange_write _ _ 448 480 UInt256.size
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))) (Or.inr (by omega))
      have finalLow : WordMemoryRange returned (value.toByteArray.write 0 returned 416 32) 224 416 :=
        wordMemoryRange_write _ _ 416 224 416
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num))) (Or.inl (by omega))
      have finalHigh : WordMemoryRange returned (value.toByteArray.write 0 returned 416 32) 480 UInt256.size :=
        wordMemoryRange_write _ _ 416 480 UInt256.size
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num))) (Or.inr (by omega))
      refine Or.inl ⟨evm', σ', _, _, value, aw2, out, k2, C2,
        vaultConversionPrefixComputed (by simpa only [hmax] using harg) hbody, hs',
        store_get_self _ _ _, ?_, ?_, ?_, ?_, ?_, rdNext⟩
      · intro name htotal hcall
        rw [store_get_ne _ _ (beq_eq_false_iff_ne.mpr (Ne.symm htotal)),
          store_get_ne _ _ (beq_eq_false_iff_ne.mpr (Ne.symm hcall)),
          store_get_ne _ _ (beq_eq_false_iff_ne.mpr (Ne.symm htotal))]
      · exact ((preLow.trans (frameScratch.mono (by omega) (by decide +kernel))).trans returnLow).trans finalLow
      · exact ((preHigh.trans (frameScratch.mono (by omega) (by omega))).trans returnHigh).trans finalHigh
      · exact toByteArray_write_size_ge_off_add32 _ _ 416
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num)))
      · exact memLoad_write_back _ _ 416 (by decide +kernel)
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num)))
    · exact Or.inr ⟨vaultConversionPrefixReverted (by simpa only [hmax] using harg) hbody, hrev⟩
  · obtain ⟨aw', k', C', rdNext⟩ := hprovided hmax h
    refine Or.inl ⟨evm, σ, _, preMem, total, aw', rdata, k', C',
      vaultConversionPrefixProvided harg hmax, hs, store_get_self _ _ _, ?_, preLow, preHigh, preSize, ?_, rdNext⟩
    · intro name htotal _
      exact store_get_ne _ _ (beq_eq_false_iff_ne.mpr (Ne.symm htotal))
    · exact memLoad_write_back _ _ 416 (by decide +kernel)
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num)))

theorem vaultConvertSharesPrepare {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm)
    (harg : locals.get? "_total_assets" = some (.int (Int.ofNat total.toNat)))
    (hread : memLoad (UInt256.ofNat 384) mem = total)
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7108) R mem aw rdata σ k C) :
    vaultConversionPrefixOutcome fork s0 evm I g locals mem (UInt256.ofNat 7145) R := by
  have hword : memLoad (UInt256.ofNat 416)
      ((memLoad (UInt256.ofNat 384) mem).toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32) = total := by
    rw [hread]
    exact memLoad_write_back _ _ 416 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num)))
  apply vaultConversionPrepare (returnPc := UInt256.ofNat 7136) hs harg hstack (by native_decide) ?_ ?_ ?_ h
  · intro hne rd
    have rdNext := vaultBlocks.vault_block_7108_taken (by omega)
      (by rw [hword]; intro hnot; exact hne ((u256_lnot_eq_zero_iff _).mp hnot)) (by native_decide) rd
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7145) R
      ((memLoad (UInt256.ofNat 384) mem).toByteArray.write 0 mem 416 32) _ rdata σ _ _ at rdNext
    rw [hread] at rdNext
    exact ⟨_, _, _, rdNext⟩
  · intro hmax rd
    have rdCall := vaultBlocks.vault_block_7108_fallthrough (by omega)
      (by rw [hword]; exact (u256_lnot_eq_zero_iff _).mpr hmax) rd
    have rdCallee := vaultBlocks.vault_block_7126 (by omega) (by native_decide) rdCall
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 6772)
      (UInt256.ofNat 448 :: UInt256.ofNat 7136 :: R)
      ((memLoad (UInt256.ofNat 384) mem).toByteArray.write 0 mem 416 32) _ rdata σ _ _ at rdCallee
    rw [hread] at rdCallee
    exact ⟨_, _, _, rdCallee⟩
  · intro mem' aw' out σ' k' C' rd
    have rdNext := vaultBlocks.vault_block_7136 (by omega) rd
    exact ⟨_, _, _, rdNext⟩

theorem vaultConvertAssetsPrepare {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm)
    (harg : locals.get? "_total_assets" = some (.int (Int.ofNat total.toNat)))
    (hread : memLoad (UInt256.ofNat 384) mem = total)
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7332) R mem aw rdata σ k C) :
    vaultConversionPrefixOutcome fork s0 evm I g locals mem (UInt256.ofNat 7369) R := by
  have hword : memLoad (UInt256.ofNat 416)
      ((memLoad (UInt256.ofNat 384) mem).toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32) = total := by
    rw [hread]
    exact memLoad_write_back _ _ 416 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num)))
  apply vaultConversionPrepare (returnPc := UInt256.ofNat 7360) hs harg hstack (by native_decide) ?_ ?_ ?_ h
  · intro hne rd
    have rdNext := vaultBlocks.vault_block_7332_taken (by omega)
      (by rw [hword]; intro hnot; exact hne ((u256_lnot_eq_zero_iff _).mp hnot)) (by native_decide) rd
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7369) R
      ((memLoad (UInt256.ofNat 384) mem).toByteArray.write 0 mem 416 32) _ rdata σ _ _ at rdNext
    rw [hread] at rdNext
    exact ⟨_, _, _, rdNext⟩
  · intro hmax rd
    have rdCall := vaultBlocks.vault_block_7332_fallthrough (by omega)
      (by rw [hword]; exact (u256_lnot_eq_zero_iff _).mpr hmax) rd
    have rdCallee := vaultBlocks.vault_block_7350 (by omega) (by native_decide) rdCall
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 6772)
      (UInt256.ofNat 448 :: UInt256.ofNat 7360 :: R)
      ((memLoad (UInt256.ofNat 384) mem).toByteArray.write 0 mem 416 32) _ rdata σ _ _ at rdCallee
    rw [hread] at rdCallee
    exact ⟨_, _, _, rdCallee⟩
  · intro mem' aw' out σ' k' C' rd
    have rdNext := vaultBlocks.vault_block_7360 (by omega) rd
    exact ⟨_, _, _, rdNext⟩
end Benchmarks.CurveVault
