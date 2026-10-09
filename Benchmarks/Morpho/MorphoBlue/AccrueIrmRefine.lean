import Benchmarks.Morpho.MorphoBlue.AccrueMathRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Refine
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {ptr elapsed ret fp : UInt256} {R : List UInt256} {spare : Nat}

theorem morphoAccrueIrmRefineWithMemory (p : MarketParamsWords) (imms : Store) (hc : p.Canonical)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 356 ≤ spare)
    (hparams : p.InMemory ptr mem) (hptr : 96 ≤ ptr.toNat)
    (hin : ptr.toNat + 160 ≤ mem.size) (hbefore : ptr.toNat + 160 ≤ fp.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13321)
      ([p.irm, elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw rdata σ k C) :
    AccrueTailRefinesWithMemory v ee g s0 p imms (accrueAfterElapsed p imms elapsed).locals evm
      accrueIrmBody ret R (spare - 224) mem fp 160 := by
  have hspace := hm.space
  have hgap := hm.gap
  obtain ⟨aw1, gasArg, k1, C1, rd1⟩ := morphoAccruePrepareCall (v := v) p hc hparams
    (by omega) hm.free hptr (by change _ < 2 ^ 256; omega) hin hbefore
    (by change _ < 2 ^ 256; omega) (by omega) h
  have hcm := hm.callData p σ ee
  have hcms := accrueCallDataMem_size p σ ee mem fp (by have hh := hm.size; omega) (by omega)
  have hcin : fp.toNat + 32 ≤ (accrueCallDataMem p σ ee mem fp).size := by rw [hcms]; omega
  obtain ⟨evm', z, out, hcall, hs', hout, hrd⟩ := morphoAccrueCall (v := v) p hc hs
    (by omega) (by omega) hm.lower hcin
    (accrueCallDataMem_read p σ ee mem fp (by have hh := hm.size; omega) (by omega)) rd1
  have hcall' : typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
      [p.value, marketStateValue evm.accountMap evm.executionEnv p.id] (z, evm', out) := by
    simpa only [hs.env, ← hs.accounts] using hcall
  by_cases hok : z = true ∧ 32 ≤ out.size
  · rw [if_pos hok] at hrd
    obtain ⟨aw2, k2, C2, rd2⟩ := hrd
    have hout' : out.size < UInt256.size := by change _ < 2 ^ 256; omega
    have hm2 := hcm.callReturn out hout' hcin (by omega : 32 ≤ spare)
    have hsCall := morphoAccrueSourceCallOk p imms elapsed evm evm' out (by simpa only [hok.1] using hcall') hok.2 hout
    let l := (accrueAfterCall p imms elapsed evm (calldataWord out 0)).locals
    have hr : l.get? "borrowRate" = some (.int (Int.ofNat (calldataWord out 0).toNat)) := store_get_self _ _ _
    have he : l.get? "elapsed" = some (.int (Int.ofNat elapsed.toNat)) := by
      simp only [l, accrueAfterCall, accrueBeforeCall, accrueAfterElapsed,
        store_get_ne (k := "borrowRate") (a := "elapsed") _ _ (by decide),
        store_get_ne (k := "marketState") (a := "elapsed") _ _ (by decide),
        store_get_ne (k := "irm") (a := "elapsed") _ _ (by decide), store_get_self]
    have hmth := morphoAccrueMathRefineWithMemory (v := v) p l imms hstack hs' hm2 (by omega)
      (accrueAfterCall_locals p imms elapsed evm (calldataWord out 0)) hr he hvalid rd2
    have heq : spare - 32 - 192 = spare - 224 := by omega
    rw [heq] at hmth
    have hab : StateBlock config
        { contract := contract, locals := (accrueAfterElapsed p imms elapsed).locals, immutables := imms }
        evm accrueIrmBody { contract := contract, locals := l, immutables := imms } evm' (accrueIrmBody.drop 3) :=
      (StateBlock.ofABlock (morphoAccrueCallPrelude p imms elapsed evm)).step hsCall
    have had := (hm.callDataAdvance p σ ee).trans (hcm.callReturnAdvance out hout' hcin)
    simpa only [Nat.zero_add, Nat.reduceAdd] using (hmth.memoryPrepend had).prepend hab
  · rw [if_neg hok] at hrd
    exact .reverted (morphoAccrueSourceCallReverts p imms elapsed evm evm' z out hcall' hok) hrd

theorem morphoAccrueIrmRefine (p : MarketParamsWords) (imms : Store) (hc : p.Canonical)
    (hstack : R.length + 40 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hb : 356 ≤ spare)
    (hparams : p.InMemory ptr mem) (hptr : 96 ≤ ptr.toNat)
    (hin : ptr.toNat + 160 ≤ mem.size) (hbefore : ptr.toNat + 160 ≤ fp.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13321)
      ([p.irm, elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw rdata σ k C) :
    AccrueTailRefines v ee g s0 p imms (accrueAfterElapsed p imms elapsed).locals evm
      accrueIrmBody ret R (spare - 224) := by
  exact (morphoAccrueIrmRefineWithMemory p imms hc hstack hs hm hb hparams hptr hin hbefore hvalid h).forget

end Refine
end Benchmarks.Morpho.MorphoBlue
