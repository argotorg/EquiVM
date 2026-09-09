import Benchmarks.Auction.CreateAuctionSuccessTrace
import Benchmarks.Auction.CreateAuctionDecodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionCreateAuction_toMintCall {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ}
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      [⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3065⟩
      [auctionMintTargetWord σ I, ⟨0⟩, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩, ⟨132⟩,
        ⟨0x1249c58b⟩, auctionMintTargetWord σ I, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionUnpauseMintSelMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have rd3005₀ := evm_run h with [jumpdest, push1 ⟨201⟩, push0, swap1]
  obtain ⟨_, _, rd3006₀⟩ := rd3005₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3006⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3006⟩
      [auctionSlotWord ⟨201⟩ σ I, ⟨0⟩, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (auctionEventMem_mload64 I) (by decide) (by evm_ov),
    dup2, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselMask :
      UInt256.land (⟨0xffffffff⟩ : UInt256) ⟨0x1249c58b⟩ = ⟨0x1249c58b⟩ := by
    native_decide
  have rd3038' := rd3038
  rw [hselMask] at rd3038'
  have rd3051 := evm_run rd3038' with [
    raw mstore 0 (auctionUnpauseMintSelMem I) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd3065₀ := evm_run rd3051 with [
    push1 ⟨4⟩, add, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (auctionUnpauseMintSelMem_mload64 I) (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8]
  have rd3065 := rd3065₀
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ by decide] at rd3065
  rw [show UInt256.sub (⟨132⟩ : UInt256) ⟨128⟩ = ⟨4⟩ by decide] at rd3065
  exact ⟨_, _, rd3065⟩

theorem auctionCreateAuction_postMintCall {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ}
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      [⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: ⟨0x1249c58b⟩ ::
          auctionMintTargetWord σ I :: ⟨1163⟩ :: ⟨413⟩ :: auctionSelWord I :: [])
        (o.write 0 (auctionUnpauseMintSelMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 5) o (cA', σ') k' C'
    ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σInit σ₀ g A I with accountMap := σ }
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land (auctionSlotWord ⟨201⟩ σ I) solcAddrMask).toNat))) "mint" 0 []
        (z,
          { initState cA gh bl σInit σ₀ g A I with
            accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd3065⟩ := auctionCreateAuction_toMintCall h
  obtain ⟨_, rd3066⟩ := rd3065.gas (by native_decide) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd3067, hosz⟩ :=
    rd3066.call (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘ
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz⟩
  · have haw : UInt256.ofNat (MachineState.M
        (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
          (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat) = (UInt256.ofNat 5) := by
      decide
    exact haw ▸ rd3067
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := auctionMintTargetWord σ I)
      (mem := auctionUnpauseMintSelMem I) (inOff := ⟨128⟩) (inSize := ⟨4⟩)
      (hdepth := ?_) (htgt := auctionMintTarget_eq (auctionSlotWord ⟨201⟩ σ I))
      (hcd := ?_) (hΘ := ?_)
    · intro h
      exact absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide)
    · exact auctionUnpauseMintEncode_eq I
    · simpa [initState, hperm, auctionMintTargetWord] using hΘ

theorem auctionCreateAuction_mintCallSuccessToDecode {cA gh bl σInit σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3078⟩
      R mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop, dup1, iszero, push2 ⟨3111⟩, jumpiNT (by decide), pop]⟩

noncomputable def auctionMintReturnMem2 (o mem : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (UInt256.land (UInt256.lnot ⟨31⟩)
    (UInt256.add (UInt256.ofNat o.size) ⟨31⟩))).toByteArray.write 0 mem 64 32

theorem auctionMintReturnMem2_read64 (o mem : ByteArray) :
    (auctionMintReturnMem2 o mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.add ⟨128⟩ (UInt256.land (UInt256.lnot ⟨31⟩)
        (UInt256.add (UInt256.ofNat o.size) ⟨31⟩))) := by
  unfold auctionMintReturnMem2
  exact toByteArray_write_read_back_of_gap _ _ 64
    (lt_of_le_of_lt (Nat.sub_le _ _) (by native_decide : 64 < USize.size))

theorem auctionMintReturnMem2_mload64 (o mem : ByteArray) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionMintReturnMem2 o mem).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionMintReturnMem2 o mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      UInt256.add ⟨128⟩ (UInt256.land (UInt256.lnot ⟨31⟩)
        (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)) := by
  apply mloadWordValue_of_readWithPadding
  · unfold auctionMintReturnMem2
    have hgap : 64 - mem.size < USize.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (by native_decide : 64 < USize.size)
    have hsz := toByteArray_write_size_ge_off_add32
      (UInt256.add ⟨128⟩ (UInt256.land (UInt256.lnot ⟨31⟩)
        (UInt256.add (UInt256.ofNat o.size) ⟨31⟩))) mem 64 hgap
    change 64 < ((UInt256.toByteArray (UInt256.add ⟨128⟩ (UInt256.land (UInt256.lnot ⟨31⟩)
      (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)))).write 0 mem 64 32).size
    omega
  · decide
  · exact auctionMintReturnMem2_read64 o mem

theorem auctionDecodeReturn_uint256_size_ge32 {out : ByteArray} {nounId : UInt256}
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat))) :
    32 ≤ out.size := by
  by_contra h
  have hshort : out.size < 32 := by omega
  have hnone := decodeReturnValue_uint256_none_short (returndata := out) hshort
  have hdec' : ABI.decodeReturnValue? abiUInt256 out =
      some (.int (Int.ofNat nounId.toNat)) := by
    simpa [uint256] using hdec
  rw [hdec'] at hnone
  cases hnone

theorem auctionDecodeReturn_uint256_size_lt_2_255 {out : ByteArray} {nounId : UInt256}
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat))) :
    out.size < (2 : Nat) ^ 255 := by
  by_contra h
  have hhuge : (2 : Nat) ^ 255 ≤ out.size := Nat.le_of_not_gt h
  have hnone := decodeReturnValue_uint256_none_huge (returndata := out) hhuge
  have hdec' : ABI.decodeReturnValue? abiUInt256 out =
      some (.int (Int.ofNat nounId.toNat)) := by
    simpa [uint256] using hdec
  rw [hdec'] at hnone
  cases hnone

theorem auctionDecodeReturn_uint256_word {out : ByteArray} {nounId : UInt256}
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat))) :
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = nounId := by
  have ho32 := auctionDecodeReturn_uint256_size_ge32 hdec
  have hohi := auctionDecodeReturn_uint256_size_lt_2_255 hdec
  have hok := decodeReturnValue_uint256_ok (returndata := out) ho32 hohi
  have hdec' : ABI.decodeReturnValue? abiUInt256 out =
      some (.int (Int.ofNat nounId.toNat)) := by
    simpa [uint256] using hdec
  have hsome :
      some (Value.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
        some (Value.int (Int.ofNat nounId.toNat)) := hok.symm.trans hdec'
  have hnat : fromByteArrayBigEndian (out.extract 0 32) = nounId.toNat := by
    injection hsome with hval
    injection hval with hint
    exact Int.ofNat.inj hint
  rw [hnat]
  exact u256_ofNat_toNat nounId

theorem auctionDecodeReturn_uint256_some_exists {out : ByteArray} {v : Value}
    (hdec : ABI.decodeReturnValue? uint256 out = some v) :
    ∃ nounId : UInt256,
      ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)) := by
  by_cases hshort : out.size < 32
  · have hnone := decodeReturnValue_uint256_none_short (returndata := out) hshort
    have hdec' : ABI.decodeReturnValue? abiUInt256 out = some v := by
      simpa [uint256] using hdec
    rw [hdec'] at hnone
    cases hnone
  · have ho32 : 32 ≤ out.size := by omega
    by_cases hhuge : (2 : Nat) ^ 255 ≤ out.size
    · have hnone := decodeReturnValue_uint256_none_huge (returndata := out) hhuge
      have hdec' : ABI.decodeReturnValue? abiUInt256 out = some v := by
        simpa [uint256] using hdec
      rw [hdec'] at hnone
      cases hnone
    · have hohi : out.size < (2 : Nat) ^ 255 := Nat.lt_of_not_ge hhuge
      let nounId : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
      have hwordLt : fromByteArrayBigEndian (out.extract 0 32) < UInt256.size :=
        fromByteArrayBigEndian_extract0_32_lt (returndata := out) ho32
      have htoNat : nounId.toNat = fromByteArrayBigEndian (out.extract 0 32) := by
        simpa [nounId] using UInt256.toNat_ofNat_of_lt hwordLt
      have hok := decodeReturnValue_uint256_ok (returndata := out) ho32 hohi
      refine ⟨nounId, ?_⟩
      simpa [uint256, nounId, htoNat] using hok

theorem auctionMintReturnMem2_callMem_size_eq160 (I : ExecutionEnv) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    (auctionMintReturnMem2 o
      (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)).size = 160 := by
  let mem := o.write 0 (auctionUnpauseMintSelMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat
  have hmem : mem.size = 160 := auctionUnpauseMintCallMem_size_eq160 I ho32 hosz
  unfold auctionMintReturnMem2
  rw [write32_eq _ mem 64 (by rw [toByteArray_size]) (by rw [hmem]; decide)]
  have hpre : (mem.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract, hmem]
    omega
  have hsrc :
      ((UInt256.toByteArray (UInt256.add ⟨128⟩ (UInt256.land (UInt256.lnot ⟨31⟩)
        (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)))).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hsuf : (mem.extract (64 + 32) mem.size).size = 64 := by
    rw [ByteArray.size_extract, hmem]
    omega
  rw [ByteArray.size_append, ByteArray.size_append, hpre, hsrc, hsuf]

theorem auctionMintReturnMem2_read128_of_callMem (I : ExecutionEnv) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    (auctionMintReturnMem2 o
      (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)).readWithPadding 128 32 =
      o.extract 0 32 := by
  let mem := o.write 0 (auctionUnpauseMintSelMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat
  have hmem : mem.size = 160 := auctionUnpauseMintCallMem_size_eq160 I ho32 hosz
  have hpres := write32_read_above
    (UInt256.toByteArray (UInt256.add ⟨128⟩ (UInt256.land (UInt256.lnot ⟨31⟩)
      (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)))) mem 64 128
      (by rw [toByteArray_size]) (by rw [hmem]; decide) (by decide)
      (by rw [hmem])
  have hread := auctionUnpauseMintCallMem_read128 I ho32 hosz
  simpa [mem, auctionMintReturnMem2] using hpres.trans hread

theorem auctionMintReturnMem2_mload128_of_decode (I : ExecutionEnv) {o : ByteArray}
    {nounId : UInt256}
    (hosz : o.size < UInt256.size)
    (hdec : ABI.decodeReturnValue? uint256 o = some (.int (Int.ofNat nounId.toNat))) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (auctionMintReturnMem2 o
            (o.write 0 (auctionUnpauseMintSelMem I) 128
              (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionMintReturnMem2 o
            (o.write 0 (auctionUnpauseMintSelMem I) 128
              (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)).readWithPadding
              (⟨128⟩ : UInt256).toNat 32))) = nounId := by
  have ho32 := auctionDecodeReturn_uint256_size_ge32 hdec
  have hsize := auctionMintReturnMem2_callMem_size_eq160 I ho32 hosz
  have hread := auctionMintReturnMem2_read128_of_callMem I ho32 hosz
  rw [if_neg]
  · change UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionMintReturnMem2 o
            (o.write 0 (auctionUnpauseMintSelMem I) 128
              (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)).readWithPadding 128 32)) =
        nounId
    rw [hread]
    exact auctionDecodeReturn_uint256_word hdec
  · apply not_or.mpr
    constructor
    · exact Nat.not_le_of_gt (by rw [hsize]; decide)
    · decide

theorem auctionCreateAuction_mintReturnToDecodeRoutine {cA gh bl σInit σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3078⟩
      R mem (UInt256.ofNat 5) o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hov : R.length + 5 ≤ 1024) :
  ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5820⟩
      (⟨128⟩ :: UInt256.add ⟨128⟩ (UInt256.ofNat o.size) :: ⟨3108⟩ :: R)
      (auctionMintReturnMem2 o mem) (UInt256.ofNat 5) o acc k' C' := by
  change auctionLoadWord mem (UInt256.ofNat 5) ⟨64⟩ = ⟨128⟩ at hfp
  have hg := auctionCreateAuctionMintReturnToDecode rd hov
  simpa only [hfp] using hg

theorem auctionCreateAuction_mintReturnDecodeOk {cA gh bl σInit σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {R : List UInt256} {retWord : UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5820⟩
      (⟨128⟩ :: UInt256.add ⟨128⟩ (UInt256.ofNat o.size) :: ⟨3108⟩ :: R)
      mem (UInt256.ofNat 5) o acc k C)
    (ho32 : 32 ≤ o.size)
    (ho : o.size < 2 ^ 255)
    (hword : (if (⟨128⟩ : UInt256).toNat ≥ mem.size ∨
          (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3108⟩
      (retWord :: R) mem (UInt256.ofNat 5) o acc k' C' := by
  exact auctionCreateAuctionMintDecodeOk rd ho32 ho hword hov

theorem auctionCreateAuction_successTail {cAInit cACur gh bl σInit σ σ₀ A I} {g : Sat256}
    {mem o : ByteArray} {k C : ℕ} {nounId : UInt256}
    (hperm : I.perm = true)
    (hadd : (UInt256.ofNat I.header.timestamp).toNat + (auctionSlotWord ⟨206⟩ σ I).toNat <
      UInt256.size)
    (h : RD auctionBytecode I g (initState cAInit gh bl σInit σ₀ g A I) ⟨3108⟩
      [nounId, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionMintReturnMem2 o mem) (UInt256.ofNat 5) o (cACur, σ) k C) :
    RDret auctionBytecode g (initState cAInit gh bl σInit σ₀ g A I)
      (cACur, auctionCreateAuctionSuccessPostMap σ I nounId
        (UInt256.ofNat I.header.timestamp)
        (UInt256.ofNat I.header.timestamp + auctionSlotWord ⟨206⟩ σ I)) ByteArray.empty := by
  obtain ⟨_, _, _, _, rd1163⟩ := auctionCreateAuctionSuccessToRet hperm (by simp)
    (by jump_dest) hadd h
  have rd413 := evm_run rd1163 with [jumpdest, jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionCreateAuction_mintCallSuccessTail
    {cAInit cACur gh bl σInit σTarget σ σ₀ A I}
    {g : Sat256} {o : ByteArray} {k C : ℕ} {nounId : UInt256}
    (hperm : I.perm = true)
    (hosz : o.size < UInt256.size)
    (hdec : ABI.decodeReturnValue? uint256 o = some (.int (Int.ofNat nounId.toNat)))
    (hadd : (UInt256.ofNat I.header.timestamp).toNat + (auctionSlotWord ⟨206⟩ σ I).toNat <
      UInt256.size)
    (rd : RD auctionBytecode I g (initState cAInit gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨1⟩ :: ⟨132⟩ :: ⟨0x1249c58b⟩ :: auctionMintTargetWord σTarget I :: ⟨1163⟩ :: ⟨413⟩ ::
        auctionSelWord I :: [])
      (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
      (UInt256.ofNat 5) o (cACur, σ) k C) :
    RDret auctionBytecode g (initState cAInit gh bl σInit σ₀ g A I)
      (cACur, auctionCreateAuctionSuccessPostMap σ I nounId
        (UInt256.ofNat I.header.timestamp)
        (UInt256.ofNat I.header.timestamp + auctionSlotWord ⟨206⟩ σ I)) ByteArray.empty := by
  obtain ⟨_, _, rd3078⟩ := auctionCreateAuction_mintCallSuccessToDecode rd (by simp)
  have hfp := auctionUnpauseMintCallMem_mload64 I hosz
  obtain ⟨_, _, rd5820⟩ := auctionCreateAuction_mintReturnToDecodeRoutine rd3078 hfp
    (by simp)
  have ho32 := auctionDecodeReturn_uint256_size_ge32 hdec
  have hohi := auctionDecodeReturn_uint256_size_lt_2_255 hdec
  have hword := auctionMintReturnMem2_mload128_of_decode I hosz hdec
  obtain ⟨_, _, rd3108⟩ := auctionCreateAuction_mintReturnDecodeOk
    (retWord := nounId) rd5820 ho32 hohi hword (by simp)
  exact auctionCreateAuction_successTail hperm hadd rd3108

set_option maxHeartbeats 10000000 in
theorem auctionCreateAuction_mintCallSuccessAddOverflowRevert
    {cAInit cACur gh bl σInit σTarget σ σ₀ A I} {g : Sat256} {o : ByteArray} {k C : ℕ}
    {nounId : UInt256}
    (hosz : o.size < UInt256.size)
    (hdec : ABI.decodeReturnValue? uint256 o = some (.int (Int.ofNat nounId.toNat)))
    (hover : UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (auctionSlotWord ⟨206⟩ σ I).toNat)
    (rd : RD auctionBytecode I g (initState cAInit gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨1⟩ :: ⟨132⟩ :: ⟨0x1249c58b⟩ :: auctionMintTargetWord σTarget I :: ⟨1163⟩ :: ⟨413⟩ ::
        auctionSelWord I :: [])
      (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
      (UInt256.ofNat 5) o (cACur, σ) k C) :
    RDrev auctionBytecode g (initState cAInit gh bl σInit σ₀ g A I) := by
  obtain ⟨_, _, rd3078⟩ := auctionCreateAuction_mintCallSuccessToDecode rd (by simp)
  have hfp := auctionUnpauseMintCallMem_mload64 I hosz
  obtain ⟨_, _, rd5820⟩ := auctionCreateAuction_mintReturnToDecodeRoutine rd3078 hfp
    (by simp)
  have ho32 := auctionDecodeReturn_uint256_size_ge32 hdec
  have hohi := auctionDecodeReturn_uint256_size_lt_2_255 hdec
  have hword := auctionMintReturnMem2_mload128_of_decode I hosz hdec
  obtain ⟨_, _, rd3108⟩ := auctionCreateAuction_mintReturnDecodeOk
    (retWord := nounId) rd5820 ho32 hohi hword (by simp)
  let start := UInt256.ofNat I.header.timestamp
  let duration := auctionSlotWord ⟨206⟩ σ I
  have rd3172 := evm_run rd3108 with [
    jumpdest, push1 ⟨1⟩, jumpdest, push2 ⟨3172⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨206⟩]
  obtain ⟨_, _, rd3176₀⟩ := rd3172.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3176⟩ : ∃ k C, RD auctionBytecode I g
      (initState cAInit gh bl σInit σ₀ g A I) ⟨3176⟩
      [duration, nounId, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionMintReturnMem2 o
        (o.write 0 (auctionUnpauseMintSelMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat))
      (UInt256.ofNat 5) o (cACur, σ) k C := by
    exact ⟨_, _, by simpa [duration, auctionSlotWord] using rd3176₀⟩
  have rd5704 := evm_run rd3176 with [
    timestamp, swap1, push0, swap1, push2 ⟨3189⟩, swap1, dup4, push2 ⟨5704⟩,
    jump (by jump_dest)]
  exact auctionCreateAuctionCheckedAddOverflow rd5704
    (by simpa [start, duration, Nat.add_comm] using hover) (by simp)

theorem auctionCreateAuction_mintReturnDecodeRevert {cA gh bl σInit σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5820⟩
      (⟨128⟩ :: UInt256.add ⟨128⟩ (UInt256.ofNat o.size) :: ⟨3108⟩ :: R)
      mem (UInt256.ofNat 5) o acc k C)
    (hbad :
      UInt256.slt (UInt256.sub (UInt256.add ⟨128⟩ (UInt256.ofNat o.size)) ⟨128⟩) ⟨32⟩ =
        ⟨1⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  exact auctionCreateAuctionMintDecodeRevert rd hbad hov

theorem auctionCreateAuction_mintCallSuccessDecodeRevert
    {cAInit cACur gh bl σInit σTarget σ σ₀ A I}
    {g : Sat256} {o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hdec : ABI.decodeReturnValue? uint256 o = none)
    (rd : RD auctionBytecode I g (initState cAInit gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨1⟩ :: ⟨132⟩ :: ⟨0x1249c58b⟩ :: auctionMintTargetWord σTarget I :: ⟨1163⟩ :: ⟨413⟩ ::
        auctionSelWord I :: [])
      (o.write 0 (auctionUnpauseMintSelMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
      (UInt256.ofNat 5) o (cACur, σ) k C) :
    RDrev auctionBytecode g (initState cAInit gh bl σInit σ₀ g A I) := by
  obtain ⟨_, _, rd3078⟩ := auctionCreateAuction_mintCallSuccessToDecode rd (by simp)
  have hfp := auctionUnpauseMintCallMem_mload64 I hosz
  obtain ⟨_, _, rd5820⟩ := auctionCreateAuction_mintReturnToDecodeRoutine rd3078 hfp
    (by simp)
  by_cases hshort : o.size < 32
  · exact auctionCreateAuction_mintReturnDecodeRevert rd5820
      (solcDecodeEndLenCheckShort_128_32 hshort) (by simp)
  · have ho32 : 32 ≤ o.size := by omega
    by_cases hhuge : (2 : Nat) ^ 255 ≤ o.size
    · exact auctionCreateAuction_mintReturnDecodeRevert rd5820
        (solcDecodeEndLenCheckHuge_128_32 hhuge hosz) (by simp)
    · have hohi : o.size < (2 : Nat) ^ 255 := Nat.lt_of_not_ge hhuge
      have hok := decodeReturnValue_uint256_ok (returndata := o) ho32 hohi
      have hnone : ABI.decodeReturnValue? abiUInt256 o = none := by
        simpa [uint256] using hdec
      rw [hok] at hnone
      cases hnone

theorem auctionCreateAuction_mintCallFailureEmptyRevert {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨0⟩ :: d0 :: d1 :: d2 :: R) mem aw ByteArray.empty acc k C)
    (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  have rd3111 := evm_run rd with [
    swap3, pop, pop, pop, dup1, iszero, push2 ⟨3111⟩,
    jumpiT (by decide) (by jump_dest), jumpdest]
  have rd5843 := evm_run rd3111 with [
    push2 ⟨3172⟩, jumpiNT (by decide), push2 ⟨3123⟩, push2 ⟨5843⟩,
    jump (by jump_dest), jumpdest]
  have rd5865 := evm_run rd5843 with [
    push0, push1 ⟨3⟩, returndatasize, gt, iszero, push2 ⟨5865⟩,
    jumpiT (by decide) (by jump_dest), jumpdest]
  have rd3123 := evm_run rd5865 with [swap1, jump (by jump_dest), jumpdest]
  have rd3165 := evm_run rd3123 with [
    dup1, push4 ⟨0x08c379a0⟩, sub, push2 ⟨3162⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, pop, jumpdest]
  have rd3166 := RD.returndatasize rd3165 (by native_decide)
    (by omega)
  have rd3167 := RD.push0 rd3166 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3168 := RD.dup1 rd3167 (by native_decide)
    (by simp only [List.length_cons]; omega)
  let len := UInt256.ofNat ByteArray.empty.size
  let memout := ByteArray.empty.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd3169 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd3168 (by decide)
    (by
      change 0 + len.toNat ≤ ByteArray.empty.size
      dsimp [len]
      decide)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by omega)
  have rd3170 := RD.returndatasize rd3169 (by native_decide) (by omega)
  have rd3171 := RD.push0 rd3170 (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd3171 (by decide)
    (fun s haws hstks => by
      simpa [awout, len, haws] using memExpRevertZeroOff s hstks)
    (by omega)

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureShortRevert {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {aw d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨0⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hshort : o.size < 4) (hosz : o.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  have rd3111 := evm_run rd with [
    swap3, pop, pop, pop, dup1, iszero, push2 ⟨3111⟩,
    jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd5843 := evm_run rd3111 with [
    push2 ⟨3172⟩, jumpiNT (by native_decide), push2 ⟨3123⟩, push2 ⟨5843⟩,
    jump (by jump_dest), jumpdest]
  have hgt : UInt256.gt (UInt256.ofNat o.size) (⟨3⟩ : UInt256) = ⟨0⟩ := by
    apply ugt_zero
    change (UInt256.ofNat o.size).toNat ≤ 3
    rw [UInt256.toNat_ofNat_of_lt hosz]
    omega
  have rd5849₀ := evm_run rd5843 with [push0, push1 ⟨3⟩, returndatasize, gt]
  have rd5849 := rd5849₀
  rw [hgt] at rd5849
  have rd5850₀ := evm_run rd5849 with [iszero]
  have rd5850 := rd5850₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5850
  have rd3123 := evm_run rd5850 with [
    push2 ⟨5865⟩, jumpiT (by native_decide) (by jump_dest), jumpdest, swap1,
    jump (by jump_dest), jumpdest]
  have rd3165 := evm_run rd3123 with [
    dup1, push4 ⟨0x08c379a0⟩, sub, push2 ⟨3162⟩,
    jumpiT (by native_decide) (by jump_dest), jumpdest, pop, jumpdest]
  have rd3166 := RD.returndatasize rd3165 (by native_decide)
    (by omega)
  have rd3167 := RD.push0 rd3166 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3168 := RD.dup1 rd3167 (by native_decide)
    (by simp only [List.length_cons]; omega)
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd3169 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd3168 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [UInt256.toNat_ofNat_of_lt hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by omega)
  have rd3170 := RD.returndatasize rd3169 (by native_decide) (by omega)
  have rd3171 := RD.push0 rd3170 (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd3171 (by native_decide)
    (fun s haws hstks => by
      simpa [awout, len, haws] using memExpRevertZeroOff s hstks)
    (by omega)

-- LIBRARY CANDIDATE: `ByteArray` `==` reflects equality.
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

theorem auctionMintFailureSelector_bridge {o mem : ByteArray}
    (hlen : 4 ≤ o.size) (hsel : o.extract 0 4 ≠ errorStringSelector) :
    ∃ preSel : UInt256,
      (if (⟨0⟩ : UInt256).toNat ≥ (o.write 0 mem 0 4).size ∨
          (⟨0⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((o.write 0 mem 0 4).readWithPadding
            (⟨0⟩ : UInt256).toNat 32))) = preSel ∧
      UInt256.shiftRight preSel ⟨224⟩ ≠ (⟨0x08c379a0⟩ : UInt256) := by
  let cd := o.write 0 mem 0 4
  let preSel := uInt256OfByteArray (ByteArray.readBytes cd 0 32)
  refine ⟨preSel, ?_, ?_⟩
  · have hdata := write0_data o mem 4 (by decide) hlen
    have hlenData : 4 ≤ o.data.size := by
      change 4 ≤ o.data.size
      exact hlen
    have hcdpos : 0 < cd.size := by
      dsimp [cd]
      show 0 < (o.write 0 mem 0 4).data.size
      rw [hdata, Array.size_append]
      have hs : (o.data.extract 0 4).size = 4 := by
        rw [Array.size_extract]
        exact Nat.min_eq_left hlenData
      omega
    rw [if_neg]
    · change UInt256.ofNat (fromByteArrayBigEndian (cd.readWithPadding 0 32)) = preSel
      rw [readWithPadding_zero_32_eq_readBytes]
      simp [preSel, uInt256OfByteArray_eq]
    · exact not_or.mpr ⟨Nat.not_le_of_gt hcdpos, by decide⟩
  · intro heq
    have hcdsz : 4 ≤ cd.size := by
      dsimp [cd]
      have hdata := write0_data o mem 4 (by decide) hlen
      have hlenData : 4 ≤ o.data.size := by
        change 4 ≤ o.data.size
        exact hlen
      show 4 ≤ (o.write 0 mem 0 4).data.size
      rw [hdata, Array.size_append]
      have hs : (o.data.extract 0 4).size = 4 := by
        rw [Array.size_extract]
        exact Nat.min_eq_left hlenData
      omega
    have hprefix : cd.extract 0 4 = o.extract 0 4 := by
      have hread := write0_read_back_gen o mem 4 (by decide) hlen (by norm_num)
      have hcdExtract : cd.readWithPadding 0 4 = cd.extract 0 4 := by
        exact readWithPadding_eq_extract' cd 0 4 (by norm_num) (by norm_num)
          (by simpa [cd] using hcdsz)
      rw [← hcdExtract]
      simpa [cd] using hread
    have hbeq : ((⟨#[0x08, 0xc3, 0x79, 0xa0]⟩ : ByteArray) == cd.extract 0 4) =
        false := by
      cases heq : ((⟨#[0x08, 0xc3, 0x79, 0xa0]⟩ : ByteArray) == cd.extract 0 4)
      · rfl
      · exfalso
        have hbyte := byteArray_eq_of_beq heq
        rw [hprefix] at hbyte
        exact hsel (by simpa [errorStringSelector] using hbyte.symm)
    have hdec := evmSelectorDecode (cd := cd) hcdsz 0x08 0xc3 0x79 0xa0
      (⟨0x08c379a0⟩ : UInt256) (by decide)
    simp [hbeq] at hdec
    have heqSym : UInt256.eq (⟨0x08c379a0⟩ : UInt256)
        (UInt256.shiftRight preSel ⟨224⟩) = ⟨1⟩ := by
      rw [heq, u256_eq_refl]
    rw [hdec] at heqSym
    exact (by decide : (⟨0⟩ : UInt256) ≠ ⟨1⟩) heqSym

theorem auctionMintFailureErrorSelector_bridge {o mem : ByteArray}
    (hlen : 4 ≤ o.size) (hsel : o.extract 0 4 = errorStringSelector) :
    ∃ preSel : UInt256,
      (if (⟨0⟩ : UInt256).toNat ≥ (o.write 0 mem 0 4).size ∨
          (⟨0⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((o.write 0 mem 0 4).readWithPadding
            (⟨0⟩ : UInt256).toNat 32))) = preSel ∧
      UInt256.shiftRight preSel ⟨224⟩ = (⟨0x08c379a0⟩ : UInt256) := by
  let cd := o.write 0 mem 0 4
  let preSel := uInt256OfByteArray (ByteArray.readBytes cd 0 32)
  refine ⟨preSel, ?_, ?_⟩
  · have hdata := write0_data o mem 4 (by decide) hlen
    have hlenData : 4 ≤ o.data.size := by
      change 4 ≤ o.data.size
      exact hlen
    have hcdpos : 0 < cd.size := by
      dsimp [cd]
      show 0 < (o.write 0 mem 0 4).data.size
      rw [hdata, Array.size_append]
      have hs : (o.data.extract 0 4).size = 4 := by
        rw [Array.size_extract]
        exact Nat.min_eq_left hlenData
      omega
    rw [if_neg]
    · change UInt256.ofNat (fromByteArrayBigEndian (cd.readWithPadding 0 32)) = preSel
      rw [readWithPadding_zero_32_eq_readBytes]
      simp [preSel, uInt256OfByteArray_eq]
    · exact not_or.mpr ⟨Nat.not_le_of_gt hcdpos, by decide⟩
  · have hcdsz : 4 ≤ cd.size := by
      dsimp [cd]
      have hdata := write0_data o mem 4 (by decide) hlen
      have hlenData : 4 ≤ o.data.size := by
        change 4 ≤ o.data.size
        exact hlen
      show 4 ≤ (o.write 0 mem 0 4).data.size
      rw [hdata, Array.size_append]
      have hs : (o.data.extract 0 4).size = 4 := by
        rw [Array.size_extract]
        exact Nat.min_eq_left hlenData
      omega
    have hprefix : cd.extract 0 4 = o.extract 0 4 := by
      have hread := write0_read_back_gen o mem 4 (by decide) hlen (by norm_num)
      have hcdExtract : cd.readWithPadding 0 4 = cd.extract 0 4 := by
        exact readWithPadding_eq_extract' cd 0 4 (by norm_num) (by norm_num)
          (by simpa [cd] using hcdsz)
      rw [← hcdExtract]
      simpa [cd] using hread
    have hbeq : ((⟨#[0x08, 0xc3, 0x79, 0xa0]⟩ : ByteArray) == cd.extract 0 4) = true := by
      rw [hprefix, hsel]
      native_decide
    have hdec := evmSelectorDecode (cd := cd) hcdsz 0x08 0xc3 0x79 0xa0
      (⟨0x08c379a0⟩ : UInt256) (by decide)
    simp [hbeq] at hdec
    exact (uInt256_eq_one_eq hdec).symm

theorem auctionCreateAuction_callDepthLimitRevert {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {k C : ℕ}
    (hdepth : I.depth = 1024)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      [⟨1163⟩, ⟨413⟩, auctionSelWord I]
      (auctionEventMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  obtain ⟨_, _, rd3065⟩ := auctionCreateAuction_toMintCall rd
  obtain ⟨_, rd3066⟩ := rd3065.gas (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3067⟩ := rd3066.callDepthLimit (by decide) hdepth (by evm_ov)
  exact auctionCreateAuction_mintCallFailureEmptyRevert rd3067 (by simp)

end Auction
