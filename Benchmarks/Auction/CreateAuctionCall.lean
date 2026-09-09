import Benchmarks.Auction.UnpauseMintTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def auctionCreateAuctionMintSelMemAt (mem : ByteArray) (free : UInt256) :
    ByteArray :=
  (UInt256.toByteArray auctionUnpauseMintSelectorWord).write 0 mem free.toNat 32

theorem auctionCreateAuctionMintSelMemAt_encode (mem : ByteArray) (free : UInt256)
    (hlo : free.toNat ≤ mem.size) :
    auctionConfig.externalABI.encode? "mint" [] =
      some ((auctionCreateAuctionMintSelMemAt mem free).readWithPadding free.toNat 4) := by
  rw [auctionExternalABI_encode_mint]
  congr
  rw [auctionCreateAuctionMintSelMemAt]
  rw [write32_read_prefix_len _ _ free.toNat 4 (by rw [toByteArray_size]) hlo
    (by decide) (by decide) (by decide)]
  exact auctionUnpauseMintSelectorWord_prefix.symm

theorem auctionCreateAuction_toMintCallAt {cA cACur gh bl σInit σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw ret : UInt256} {R : List UInt256} {k C : ℕ}
    (hov : R.length + 20 ≤ 1024)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      (ret :: R) mem aw rdata (cACur, σ) k C) :
    let free :=
      if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
    let awLoad := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let memSel := auctionCreateAuctionMintSelMemAt mem free
    let awSel := UInt256.ofNat (MachineState.M awLoad.toNat free.toNat 32)
    let free2 :=
      if (⟨64⟩ : UInt256).toNat ≥ memSel.size ∨ (⟨64⟩ : UInt256) ≥ awSel * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat
          (fromByteArrayBigEndian (memSel.readWithPadding (⟨64⟩ : UInt256).toNat 32))
    let awLoad2 := UInt256.ofNat (MachineState.M awSel.toNat (⟨64⟩ : UInt256).toNat 32)
    let freePlus4 := (⟨4⟩ : UInt256) + free
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3065⟩
      (auctionMintTargetWord σ I :: ⟨0⟩ :: free2 :: UInt256.sub freePlus4 free2 ::
        free2 :: ⟨32⟩ :: freePlus4 :: ⟨0x1249c58b⟩ :: auctionMintTargetWord σ I ::
        ret :: R)
      memSel awLoad2 rdata (cACur, σ) k' C' := by
  intro free awLoad memSel awSel free2 awLoad2 freePlus4
  have rd3005₀ := evm_run h with [jumpdest, push1 ⟨201⟩, push0, swap1]
  obtain ⟨_, _, rd3006₀⟩ := rd3005₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3006⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3006⟩
      (auctionSlotWord ⟨201⟩ σ I :: ⟨0⟩ :: ret :: R) mem aw rdata (cACur, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3006₀⟩
  have rd3031₀ := evm_run rd3006 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have hdiv :
      UInt256.div (auctionSlotWord ⟨201⟩ σ I)
        (UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩) =
      auctionSlotWord ⟨201⟩ σ I := by
    apply u256_inj
    rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ by native_decide]
    rw [udiv_toNat]
    exact Nat.div_one (auctionSlotWord ⟨201⟩ σ I).toNat
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hmaskIdem :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨201⟩ σ I)) =
        auctionMintTargetWord σ I := by
    rw [auctionMintTargetWord]
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨201⟩ σ I)]
    exact solcAddrMask_clean_left
      (solcAddrMask_result_canonical (auctionSlotWord ⟨201⟩ σ I))
  have rd3031 := rd3031₀
  rw [hdiv, hmaskConst, hmaskIdem] at rd3031
  have rd3038 := evm_run rd3031 with [
    push4 ⟨0x1249c58b⟩, push1 ⟨64⟩,
    raw mload (Cₘ awLoad - Cₘ aw) free awLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup2, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselMask :
      UInt256.land (⟨0xffffffff⟩ : UInt256) ⟨0x1249c58b⟩ = ⟨0x1249c58b⟩ := by
    native_decide
  have rd3038' := rd3038
  rw [hselMask] at rd3038'
  have rd3051 := evm_run rd3038' with [
    raw mstore (Cₘ awSel - Cₘ awLoad) memSel awSel (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  have rd3065₀ := evm_run rd3051 with [
    push1 ⟨4⟩, add, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload (Cₘ awLoad2 - Cₘ awSel) free2 awLoad2 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8]
  exact ⟨_, _, by simpa [freePlus4] using rd3065₀⟩

theorem auctionCreateAuction_mintCallAt {cA cACur gh bl σInit σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw inOff inSize outOff outSize next selector ret : UInt256}
    {R : List UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 20 ≤ 1024)
    (hcd : auctionConfig.externalABI.encode? "mint" [] =
      some (mem.readWithPadding inOff.toNat inSize.toNat))
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3065⟩
      (auctionMintTargetWord σ I :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize ::
        next :: selector :: auctionMintTargetWord σ I :: ret :: R)
      mem aw rdata (cACur, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: next :: selector :: auctionMintTargetWord σ I ::
          ret :: R)
        (o.write 0 mem outOff.toNat (min outSize (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
            outOff.toNat outSize.toNat))
        o (cA', σ') k' C'
    ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σInit σ₀ g A I with accountMap := σ, createdAccounts := cACur }
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land (auctionSlotWord ⟨201⟩ σ I) solcAddrMask).toNat))) "mint" 0 []
        (z,
          { initState cA gh bl σInit σ₀ g A I with
            accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, rd3066⟩ := rd.gas (by native_decide) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd3067, hosz⟩ :=
    rd3066.call (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘ
  refine ⟨cA', σ', z, o, A', k', C', rd3067, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := true) (targetWord := auctionMintTargetWord σ I)
    (mem := mem) (inOff := inOff) (inSize := inSize)
    (hdepth := ?_) (htgt := auctionMintTarget_eq (auctionSlotWord ⟨201⟩ σ I))
    (hcd := hcd) (hΘ := ?_)
  · intro h
    exact absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide)
  · simpa [initState, hperm, auctionMintTargetWord] using hΘ

theorem auctionCreateAuction_postMintCallAt {cA cACur gh bl σInit σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw ret : UInt256} {R : List UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 20 ≤ 1024)
    (hcd :
      let free :=
        if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else
          UInt256.ofNat
            (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
      let awLoad := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let memSel := auctionCreateAuctionMintSelMemAt mem free
      let awSel := UInt256.ofNat (MachineState.M awLoad.toNat free.toNat 32)
      let free2 :=
        if (⟨64⟩ : UInt256).toNat ≥ memSel.size ∨ (⟨64⟩ : UInt256) ≥ awSel * ⟨32⟩ then
          ⟨0⟩
        else
          UInt256.ofNat
            (fromByteArrayBigEndian (memSel.readWithPadding (⟨64⟩ : UInt256).toNat 32))
      let freePlus4 := (⟨4⟩ : UInt256) + free
      auctionConfig.externalABI.encode? "mint" [] =
        some (memSel.readWithPadding free2.toNat (UInt256.sub freePlus4 free2).toNat))
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      (ret :: R) mem aw rdata (cACur, σ) k C) :
    let free :=
      if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
    let awLoad := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let memSel := auctionCreateAuctionMintSelMemAt mem free
    let awSel := UInt256.ofNat (MachineState.M awLoad.toNat free.toNat 32)
    let free2 :=
      if (⟨64⟩ : UInt256).toNat ≥ memSel.size ∨ (⟨64⟩ : UInt256) ≥ awSel * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat
          (fromByteArrayBigEndian (memSel.readWithPadding (⟨64⟩ : UInt256).toNat 32))
    let awLoad2 := UInt256.ofNat (MachineState.M awSel.toNat (⟨64⟩ : UInt256).toNat 32)
    let freePlus4 := (⟨4⟩ : UInt256) + free
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: freePlus4 :: ⟨0x1249c58b⟩ ::
          auctionMintTargetWord σ I :: ret :: R)
        (o.write 0 memSel free2.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat
          (MachineState.M
            (MachineState.M awLoad2.toNat free2.toNat
              (UInt256.sub freePlus4 free2).toNat)
            free2.toNat (⟨32⟩ : UInt256).toNat))
        o (cA', σ') k' C'
    ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σInit σ₀ g A I with accountMap := σ, createdAccounts := cACur }
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land (auctionSlotWord ⟨201⟩ σ I) solcAddrMask).toNat))) "mint" 0 []
        (z,
          { initState cA gh bl σInit σ₀ g A I with
            accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  intro free awLoad memSel awSel free2 awLoad2 freePlus4
  obtain ⟨_, _, rd3065⟩ := auctionCreateAuction_toMintCallAt hov h
  exact auctionCreateAuction_mintCallAt hperm hdepth hov hcd rd3065


end Auction
