import Benchmarks.CurveVault.Common
import Benchmarks.CurveVault.RuntimeBlocks_001
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

/-! The shared calldata/payability guard and computed jump at pcs 73–98. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

theorem vaultGuardPass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {entry pc : UInt256} {R : List UInt256} {minSize : Nat}
    (hstack : R.length + 5 ≤ 1024)
    (hpayable : UInt256.land (UInt256.ofNat 1) entry = ⟨1⟩)
    (hminimum : UInt256.land (UInt256.ofNat 254) entry = UInt256.ofNat minSize)
    (htarget : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight entry (UInt256.ofNat 8)) = pc)
    (hvalid : (D_J vaultBytecode 0).contains pc = true)
    (hvalue : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hargs : minSize ≤ I.calldata.size)
    (h : RD fork vaultBytecode I g s0 ⟨73⟩ (entry :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork vaultBytecode I g s0 pc (entry :: R) mem aw rdata σ k' C' := by
  have hlt : UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat minSize) = ⟨0⟩ := by
    apply ult_zero
    rw [ulit_toNat' _ hsize, ulit_toNat' _ (Nat.lt_of_le_of_lt hargs hsize)]
    exact hargs
  have rd90 := vaultBlocks.vault_block_73_fallthrough hstack
    (by rw [hpayable, hminimum, hvalue, u256_one_mul, hlt, u256_lor_zero]; rfl) h
  have rdBody := vaultBlocks.vault_block_90 (by omega)
    (by rw [htarget]; exact hvalid) rd90
  exact ⟨_, _, by simpa only [htarget] using rdBody⟩

theorem vaultGuardNonpayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {entry : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hpayable : UInt256.land (UInt256.ofNat 1) entry = ⟨1⟩)
    (hvalue : I.weiValue ≠ ⟨0⟩)
    (h : RD fork vaultBytecode I g s0 ⟨73⟩ (entry :: R) mem aw rdata σ k C) :
    RDrev fork vaultBytecode g s0 := by
  have rdRevert := vaultBlocks.vault_block_73_taken hstack
    (by rw [hpayable, u256_one_mul, u256_lor_comm]; exact u256_lor_ne_zero_right hvalue)
    (by native_decide) h
  exact vaultBlocks.vault_block_8284 (by simp only [List.length_cons]; omega) rdRevert

theorem vaultGuardShort {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {entry : UInt256} {R : List UInt256} {minSize : Nat}
    (hstack : R.length + 5 ≤ 1024)
    (hminimum : UInt256.land (UInt256.ofNat 254) entry = UInt256.ofNat minSize)
    (hbound : minSize < UInt256.size) (hshort : I.calldata.size < minSize)
    (h : RD fork vaultBytecode I g s0 ⟨73⟩ (entry :: R) mem aw rdata σ k C) :
    RDrev fork vaultBytecode g s0 := by
  have hlt : UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat minSize) = ⟨1⟩ := by
    apply ult_one
    rw [ulit_toNat' _ (Nat.lt_trans hshort hbound), ulit_toNat' _ hbound]
    exact hshort
  have rdRevert := vaultBlocks.vault_block_73_taken hstack
    (by rw [hminimum, hlt]; exact u256_lor_one_right_ne_zero _)
    (by native_decide) h
  exact vaultBlocks.vault_block_8284 (by simp only [List.length_cons]; omega) rdRevert

theorem vaultGuardedEntry {σ σ₀ A I} {g : UInt256} {t : TransitionDecl}
    {entry pc : UInt256} {mem : ByteArray} {minSize : Nat} {stmts : List Stmt}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hd : dispatchMsg contract I.calldata = some t)
    (hbody : t.body = .require (.binary .eq (.env .callvalue) (.intLit 0)) :: stmts)
    (hpayable : UInt256.land (UInt256.ofNat 1) entry = ⟨1⟩)
    (hminimum : UInt256.land (UInt256.ofNat 254) entry = UInt256.ofNat minSize)
    (hbound : minSize < UInt256.size)
    (htarget : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight entry (UInt256.ofNat 8)) = pc)
    (hvalid : (D_J vaultBytecode 0).contains pc = true)
    (hshort : I.calldata.size < minSize →
      config.externalABI.decodeCalldata? (t.params.map Param.name)
        (transitionSignature t).paramTypes I.calldata = none)
    (hreach : ∃ k C, RD fork vaultBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨73⟩ [entry, solcSelectorWord I]
      mem ⟨1⟩ ByteArray.empty σ k C)
    (htrace : I.weiValue = ⟨0⟩ → minSize ≤ I.calldata.size → ∀ k C,
      RD fork vaultBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) pc [entry, solcSelectorWord I]
        mem ⟨1⟩ ByteArray.empty σ k C → runtimeRefinementFor fork config contract σ σ₀ g A I) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨k, C, rd73⟩ := hreach
  by_cases hvalue : I.weiValue = ⟨0⟩
  · by_cases hargs : minSize ≤ I.calldata.size
    · obtain ⟨k', C', rdBody⟩ := vaultGuardPass (by simp) hpayable hminimum
        htarget hvalid hvalue hsize hargs rd73
      exact htrace hvalue hargs k' C' rdBody
    · have hlt : I.calldata.size < minSize := by omega
      exact (vaultGuardShort (by simp) hminimum hbound hlt rd73).reEquivDecodingFailed
        hcode hd (hshort hlt) rfl rfl
  · have hrev := vaultGuardNonpayable (by simp) hpayable hvalue rd73
    refine RDrev.reEquivOfDispatch hcode hd (fun _ => ?_) hrev
    rw [hbody]
    exact bodyReverts_nonPayable hvalue

/-- Assemble a nullary getter from its source expression and return trace. The common
entry guard still covers arbitrary call value, calldata suffixes, and starting gas. -/
theorem vaultNullaryReturn {σ σ₀ A I} {g : UInt256} {t : TransitionDecl}
    {entry pc : UInt256} {mem : ByteArray} {expr : Expr} {value : Value} {out : ByteArray}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz : 4 ≤ I.calldata.size)
    (hd : dispatchMsg contract I.calldata = some t)
    (hparams : t.params = [])
    (hbody : t.body = [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [expr]])
    (heval : evalExpr? config {contract := contract, locals := ∅}
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) expr = .ok value)
    (hencode : returnEquiv out (some [value]) t.returnType)
    (hpayable : UInt256.land (UInt256.ofNat 1) entry = ⟨1⟩)
    (hminimum : UInt256.land (UInt256.ofNat 254) entry = UInt256.ofNat 4)
    (htarget : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight entry (UInt256.ofNat 8)) = pc)
    (hvalid : (D_J vaultBytecode 0).contains pc = true)
    (hreach : ∃ k C, RD fork vaultBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨73⟩ [entry, solcSelectorWord I]
      mem ⟨1⟩ ByteArray.empty σ k C)
    (htrace : ∀ k C, RD fork vaultBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) pc [entry, solcSelectorWord I]
      mem ⟨1⟩ ByteArray.empty σ k C →
      RDret fork vaultBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  apply vaultGuardedEntry hcode hsize hd hbody hpayable hminimum
    (by decide +kernel : 4 < UInt256.size) htarget hvalid
    (fun h => False.elim (by omega)) hreach
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper (t.params.map Param.name)
      (t.params.map (fun p => p.ty)) I.calldata = some ∅
    rw [hparams]
    exact decodeCalldataWithMode_empty_ok hsz
  have hsource := nonpayableReturnExprBodyReturns (fork := fork) (contract := contract)
    (locals := (∅ : Store)) hvalue heval
  rw [← hbody] at hsource
  exact (htrace k C rdBody).reEquivExecution hcode hd hdec hsource hencode

end Benchmarks.CurveVault
