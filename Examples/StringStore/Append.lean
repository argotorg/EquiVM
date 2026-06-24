import Examples.StringStore.CurrentLength

/-!
# StringStore — `appendToHistory(string)` branch scaffolding
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

theorem stringStoreDispatch_appendToHistory {cd : ByteArray}
    (hsel : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some appendToHistoryTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition])
    (post := [replaceFromHistoryTransition, dropLastTransition, clearCurrentTransition,
      clearAllTransition, storeRawTransition, currentLengthGetter, historyLengthGetter,
      rawLengthGetter]) rfl ?_
    (by rw [selectorOf, appendToHistorySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide

theorem stringStoreReachAppendToHistory {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨364⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreHighMatches 0 (by omega) hsz hsel
  exact stringStoreReachHighBody 0 (by omega) ⟨364⟩ hcode hwv hsz hsize
    (stringStorePivotNotTaken 0 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem stringStoreReachAppendToHistoryDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2815⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨385⟩, ⟨390⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k0, C0, hreach⟩ := stringStoreReachAppendToHistory
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hsizeWord :
      (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size := by
    exact uadd_lit_usub_ofNat_lit hsz hsize
  exact ⟨_, _, by
    simpa [hsizeWord] using
      (evm_run hreach with [
        jumpdest, push2 ⟨390⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
        push2 ⟨385⟩, swap2, swap1, push2 ⟨2815⟩,
        jump (by jump_dest) ])⟩

theorem stringStoreX_appendToHistoryDecoderHeadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hshort : I.calldata.size < 36) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachAppendToHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2836⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_appendToHistoryDecoderHeadHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachAppendToHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2836⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_appendToHistoryDecoderOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachAppendToHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd2842 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd2851 := RD.pushConst rd2842 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd2851 with [
    dup2, gt, iszero, push2 ⟨2866⟩,
    jumpiNT (by rw [hgt']; decide),
    push2 ⟨2865⟩, push2 ⟨2410⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_appendStringDecoder2730LengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2730⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨2751⟩,
    jumpiNT (by exact hstart),
    push2 ⟨2750⟩, push2 ⟨2718⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_appendStringDecoder2730PayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2730⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlenMax :
      UInt256.gt (uInt256OfByteArray (I.calldata.readBytes start.toNat 32))
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt ((start + ⟨32⟩) +
          UInt256.mul (uInt256OfByteArray (I.calldata.readBytes start.toNat 32)) ⟨1⟩)
        ennd = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2751 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨2751⟩,
    jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd2765 := RD.pushConst (evm_run rd2751 with [jumpdest, dup3, calldataload, swap1, pop])
    ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd2765 with [
    dup2, gt, iszero, push2 ⟨2780⟩,
    jumpiT (by rw [hlenMax]; decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨1⟩, dup3, mul, dup4, add, gt, iszero, push2 ⟨2808⟩,
    jumpiNT (by rw [hpayload]; decide),
    push2 ⟨2807⟩, push2 ⟨2726⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_appendStringDecoder2730LengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2730⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlenMax :
      UInt256.gt (uInt256OfByteArray (I.calldata.readBytes start.toNat 32))
        ⟨18446744073709551615⟩ = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2751 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨2751⟩,
    jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd2765 := RD.pushConst (evm_run rd2751 with [jumpdest, dup3, calldataload, swap1, pop])
    ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd2765 with [
    dup2, gt, iszero, push2 ⟨2780⟩,
    jumpiNT (by rw [hlenMax]; decide),
    push2 ⟨2779⟩, push2 ⟨2722⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_appendStringDecoder2730Ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2730⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlenMax :
      UInt256.gt (uInt256OfByteArray (I.calldata.readBytes start.toNat 32))
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt ((start + ⟨32⟩) +
          UInt256.mul (uInt256OfByteArray (I.calldata.readBytes start.toNat 32)) ⟨1⟩)
        ennd = ⟨0⟩)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (uInt256OfByteArray (I.calldata.readBytes start.toNat 32) ::
        (start + ⟨32⟩) :: headOff :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2751 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨2751⟩,
    jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd2765 := RD.pushConst (evm_run rd2751 with [jumpdest, dup3, calldataload, swap1, pop])
    ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd2808 := evm_run rd2765 with [
    dup2, gt, iszero, push2 ⟨2780⟩,
    jumpiT (by rw [hlenMax]; decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨1⟩, dup3, mul, dup4, add, gt, iszero, push2 ⟨2808⟩,
    jumpiT (by rw [hpayload]; decide) (by jump_dest)]
  exact ⟨_, _, by
    simpa using
      (evm_run rd2808 with [
        jumpdest, swap3, pop, swap3, swap1, pop, jump hret])⟩

set_option maxHeartbeats 1200000 in
theorem stringStoreX_appendToHistoryDecoderLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachAppendToHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffLeMax : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord I.calldata 4).toNat < 2 ^ 255 := by
    omega
  have hstart31ToNat :
      ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩).toNat) =
        4 + (calldataWord I.calldata 4).toNat + 31 := by
    have hoffSize : (calldataWord I.calldata 4).toNat < UInt256.size :=
      (calldataWord I.calldata 4).val.isLt
    have hoffOfNat :
        (UInt256.ofNat (calldataWord I.calldata 4).toNat).toNat =
          (calldataWord I.calldata 4).toNat :=
      ulit_toNat' _ hoffSize
    rw [← u256_ofNat_toNat (calldataWord I.calldata 4)]
    simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
      (b := (calldataWord I.calldata 4).toNat)
      (c := 31)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign hoffSmall)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign (by omega : 4 + (calldataWord I.calldata 4).toNat < 2 ^ 255))
      (lt_size_of_lt_sign (by omega :
        4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255)))
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · apply slt_lit_zero hsizeSign
      · rw [hstart31ToNat]
        omega
      · rw [hstart31ToNat]
        omega
    · apply slt_zero_of_left_low_right_high
      · rw [hstart31ToNat]
        omega
      · rw [ulit_toNat' I.calldata.size hsize]
        omega
  have rd2842 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd2851 := RD.pushConst rd2842 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd2866 := evm_run rd2851 with [
    dup2, gt, iszero, push2 ⟨2866⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd2730 := evm_run rd2866 with [
    jumpdest, push2 ⟨2878⟩, dup6, dup3, dup7, add, push2 ⟨2730⟩,
    jump (by jump_dest)]
  exact stringStoreX_appendStringDecoder2730LengthShort rd2730
    (by simpa [calldataWord] using hstart) (by evm_ov)

theorem stringStoreX_appendToHistoryDecoderPayloadShortCore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachAppendToHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have rd2842 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd2851 := RD.pushConst rd2842 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd2866 := evm_run rd2851 with [
    dup2, gt, iszero, push2 ⟨2866⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd2730 := evm_run rd2866 with [
    jumpdest, push2 ⟨2878⟩, dup6, dup3, dup7, add, push2 ⟨2730⟩,
    jump (by jump_dest)]
  exact stringStoreX_appendStringDecoder2730PayloadShort rd2730
    (by simpa [calldataWord] using hstart)
    (by simpa [calldataWord] using hlenMax)
    (by simpa [calldataWord] using hpayload)
    (by evm_ov)

theorem stringStoreX_appendToHistoryDecoderOkCore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩),
        ⟨390⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachAppendToHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have rd2842 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd2851 := RD.pushConst rd2842 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd2866 := evm_run rd2851 with [
    dup2, gt, iszero, push2 ⟨2866⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd2730 := evm_run rd2866 with [
    jumpdest, push2 ⟨2878⟩, dup6, dup3, dup7, add, push2 ⟨2730⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd2878⟩ := stringStoreX_appendStringDecoder2730Ok rd2730
    (by simpa [calldataWord] using hstart)
    (by simpa [calldataWord] using hlenMax)
    (by simpa [calldataWord] using hpayload)
    (by jump_dest)
    (by evm_ov)
  have rd385 := evm_run rd2878 with [
    jumpdest, swap3, pop, swap3, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [calldataWord] using
      (evm_run rd385 with [jumpdest, push2 ⟨1759⟩, jump (by jump_dest)])⟩

theorem stringStoreX_appendToHistoryReachMemoryAlloc {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1759⟩
      [len, payloadStart, ret, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1780⟩
        [ ⟨64⟩,
          ⟨32⟩ + (((⟨31⟩ : UInt256) + len) / ⟨32⟩) * ⟨32⟩,
          len, len, payloadStart, ⟨0⟩, ⟨0⟩, len, payloadStart, ret,
          stringStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1780 := evm_run rd with [
    jumpdest, push0, push0, dup4, dup4, dup1, dup1, push1 ⟨31⟩, add,
    push1 ⟨32⟩, dup1, swap2, div, mul, push1 ⟨32⟩, add,
    push1 ⟨64⟩]
  exact ⟨_, _, by simpa using rd1780⟩

theorem stringStoreX_appendToHistoryMemoryAlloc {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1780⟩
      [ ⟨64⟩,
        ⟨32⟩ + (((⟨31⟩ : UInt256) + len) / ⟨32⟩) * ⟨32⟩,
        len, len, payloadStart, ⟨0⟩, ⟨0⟩, len, payloadStart, ret,
        stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1787⟩
        [⟨128⟩, len, len, payloadStart, ⟨0⟩, ⟨0⟩, len, payloadStart, ret,
          stringStoreSelWord I]
        (currentLengthAllocMem len) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1787 := evm_run rd with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (currentLengthAllocMem len) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        simp [currentLengthAllocMem, currentLengthFreePtr, currentLengthAllocSize])
      (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [currentLengthAllocSize, currentLengthFreePtr] using rd1787⟩

theorem stringStoreX_appendToHistoryMemoryLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1787⟩
      [⟨128⟩, len, len, payloadStart, ⟨0⟩, ⟨0⟩, len, payloadStart, ret,
        stringStoreSelWord I]
      (currentLengthAllocMem len) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1795⟩
        [⟨128⟩, len, len, payloadStart, ⟨128⟩, ⟨0⟩, ⟨0⟩, len, payloadStart, ret,
          stringStoreSelWord I]
        (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
  have rd1795 := evm_run rd with [
    dup1, swap4, swap3, swap2, swap1, dup2, dup2,
    raw mstore 6 (currentLengthMem len) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd1795⟩

noncomputable def appendToHistoryCalldataMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  cd.write payloadStart.toNat (currentLengthMem len) 160 len.toNat

noncomputable def appendToHistoryPaddedMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (appendToHistoryCalldataMem cd len payloadStart) ((⟨160⟩ : UInt256) + len).toNat 32

theorem stringStoreX_appendToHistoryCalldataCopy {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1795⟩
      [⟨128⟩, len, len, payloadStart, ⟨128⟩, ⟨0⟩, ⟨0⟩, len, payloadStart, ret,
        stringStoreSelWord I]
      (currentLengthMem len) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1804⟩
        [len, payloadStart, ⟨160⟩, len, len, payloadStart, ⟨128⟩, ⟨0⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryCalldataMem I.calldata len payloadStart)
        (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat))
        ByteArray.empty (cA, σ) k' C' := by
  have rd1803 := evm_run rd with [
    push1 ⟨32⟩, add, dup4, dup4, dup1, dup3, dup5]
  have hcopyDest : (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 := by
    decide
  let awout : UInt256 :=
    UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)
  have hawout :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat (⟨160⟩ : UInt256).toNat len.toNat) =
        awout := by
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
  have rd1804 := RD.calldatacopy
    (Cₘ awout - Cₘ (UInt256.ofNat 5))
    (appendToHistoryCalldataMem I.calldata len payloadStart)
    awout
    rd1803 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awout, hcopyDest])
    (by
      rw [hcopyDest]
      rfl)
    hawout
    (by evm_ov)
  exact ⟨_, _, by simpa [awout] using rd1804⟩

theorem stringStoreX_appendToHistoryMemoryPadding {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1804⟩
      [len, payloadStart, ⟨160⟩, len, len, payloadStart, ⟨128⟩, ⟨0⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryCalldataMem I.calldata len payloadStart)
      (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat))
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1809⟩
        [len, payloadStart, ⟨160⟩, len, len, payloadStart, ⟨128⟩, ⟨0⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryPaddedMem I.calldata len payloadStart)
        (UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
            (((⟨160⟩ : UInt256) + len).toNat) 32))
        ByteArray.empty (cA, σ) k' C' := by
  have rd1808 := evm_run rd with [push0, dup2, dup5, add]
  let awin : UInt256 := UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)
  let awout : UInt256 :=
    UInt256.ofNat (MachineState.M awin.toNat (((⟨160⟩ : UInt256) + len).toNat) 32)
  have rd1809 := RD.mstore
    (Cₘ awout - Cₘ awin)
    (appendToHistoryPaddedMem I.calldata len payloadStart)
    awout
    rd1808 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awin, awout])
    (by rfl)
    (by rfl)
    (by evm_ov)
  exact ⟨_, _, by simpa [awin, awout] using rd1809⟩

theorem stringStoreX_appendToHistoryMemoryCleanup {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1809⟩
      [len, payloadStart, ⟨160⟩, len, len, payloadStart, ⟨128⟩, ⟨0⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryPaddedMem I.calldata len payloadStart)
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
          (((⟨160⟩ : UInt256) + len).toNat) 32))
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1832⟩
        [⟨128⟩, ⟨0⟩, len, payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryPaddedMem I.calldata len payloadStart)
        (UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
            (((⟨160⟩ : UInt256) + len).toNat) 32))
        ByteArray.empty (cA, σ) k' C' := by
  have rd1832 := evm_run rd with [
    push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, swap1, pop,
    dup1, dup4, add, swap3, pop, pop, pop, pop, pop, pop, pop, swap1, pop]
  exact ⟨_, _, by simpa using rd1832⟩

def appendToHistoryFirstStorageSlot : UInt256 :=
  ⟨1⟩

def appendToHistoryFirstStorageLoaded (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD appendToHistoryFirstStorageSlot ⟨0⟩)

def appendToHistoryFirstStorageValue (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  appendToHistoryFirstStorageLoaded σ I + ⟨1⟩

def appendToHistoryFirstStorageMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ appendToHistoryFirstStorageSlot
    (appendToHistoryFirstStorageValue σ I)

noncomputable def appendToHistoryHistorySlotMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  (⟨1⟩ : UInt256).toByteArray.write 0
    (appendToHistoryPaddedMem cd len payloadStart) 0 32

def appendToHistoryHistorySlotMemAw (len : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
          (((⟨160⟩ : UInt256) + len).toNat) 32)).toNat
      0 32)

noncomputable def appendToHistoryArrayDataBase
    (cd : ByteArray) (len payloadStart : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((appendToHistoryHistorySlotMem cd len payloadStart).readWithPadding 0 32)))

noncomputable def appendToHistoryNewElementSlot
    (σ : AccountMap) (I : ExecutionEnv) (cd : ByteArray) (len payloadStart : UInt256) : UInt256 :=
  appendToHistoryArrayDataBase cd len payloadStart +
    (appendToHistoryFirstStorageValue σ I - ⟨1⟩)

def appendToHistoryHelperEntryAw (len : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (appendToHistoryHistorySlotMemAw len).toNat 0 32)

def appendToHistoryHelperMloadAw (len : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (appendToHistoryHelperEntryAw len).toNat 128 32)

noncomputable def appendToHistoryHelperLoadedLen
    (cd : ByteArray) (len payloadStart : UInt256) : UInt256 :=
  if (⟨128⟩ : UInt256).toNat ≥ (appendToHistoryHistorySlotMem cd len payloadStart).size ∨
      (⟨128⟩ : UInt256) ≥ appendToHistoryHelperEntryAw len * ⟨32⟩ then
    ⟨0⟩
  else
    UInt256.ofNat (fromByteArrayBigEndian
      ((appendToHistoryHistorySlotMem cd len payloadStart).readWithPadding
        (⟨128⟩ : UInt256).toNat 32))

noncomputable def appendToHistoryExistingElementHeader
    (σ : AccountMap) (I : ExecutionEnv) (cd : ByteArray) (len payloadStart : UInt256) : UInt256 :=
  (appendToHistoryFirstStorageMap σ I).find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD
      (appendToHistoryNewElementSlot σ I cd len payloadStart) ⟨0⟩)

def appendToHistoryHelperPayloadAw (len : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (appendToHistoryHelperMloadAw len).toNat 160 32)

noncomputable def appendToHistoryHelperPayloadWord
    (cd : ByteArray) (len payloadStart : UInt256) : UInt256 :=
  if (⟨160⟩ : UInt256).toNat ≥ (appendToHistoryHistorySlotMem cd len payloadStart).size ∨
      (⟨160⟩ : UInt256) ≥ appendToHistoryHelperMloadAw len * ⟨32⟩ then
    ⟨0⟩
  else
    UInt256.ofNat (fromByteArrayBigEndian
      ((appendToHistoryHistorySlotMem cd len payloadStart).readWithPadding
        (⟨160⟩ : UInt256).toNat 32))

noncomputable def appendToHistoryShortElementWriteMap
    (σ : AccountMap) (I : ExecutionEnv) (cd : ByteArray) (len payloadStart header : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner (appendToHistoryFirstStorageMap σ I)
    (appendToHistoryNewElementSlot σ I cd len payloadStart) header

noncomputable def appendToHistoryShortReturnLength
    (σ : AccountMap) (I : ExecutionEnv) (cd : ByteArray) (len payloadStart header : UInt256) :
    UInt256 :=
  (appendToHistoryShortElementWriteMap σ I cd len payloadStart header).find? I.codeOwner
    |>.option ⟨0⟩ (fun acc => acc.storage.findD appendToHistoryFirstStorageSlot ⟨0⟩)

def appendToHistoryShortPackedHeader (payloadWord lenWord : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land payloadWord
      (UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ lenWord))))
    (UInt256.mul ⟨2⟩ lenWord)

theorem appendToHistoryHistorySlotMem_read0
    (cd : ByteArray) (len payloadStart : UInt256) :
    (appendToHistoryHistorySlotMem cd len payloadStart).readWithPadding 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [appendToHistoryHistorySlotMem]
  rw [write0_read_back_gen
    (src := UInt256.toByteArray (⟨1⟩ : UInt256))
    (base := appendToHistoryPaddedMem cd len payloadStart)
    (len := 32)
    (by decide)
    (by rw [toByteArray_size])
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem appendToHistory_write_len_zero (src base : ByteArray) (sa da : ℕ) :
    src.write sa base da 0 = base := by
  simp [ByteArray.write]

theorem appendToHistoryCalldataMem_zero (cd : ByteArray) (payloadStart : UInt256) :
    appendToHistoryCalldataMem cd ⟨0⟩ payloadStart = currentLengthMem ⟨0⟩ := by
  simp [appendToHistoryCalldataMem, appendToHistory_write_len_zero]

theorem appendToHistoryCalldataMem_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (appendToHistoryCalldataMem cd len payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  have hpres := write_read_below_end_from cd (currentLengthMem len)
    payloadStart.toNat len.toNat 128 hlen hsrc (by
      rw [currentLengthMem_size])
  rw [appendToHistoryCalldataMem, ← currentLengthMem_size len]
  exact hpres.trans (currentLengthMem_read128 len)

theorem appendToHistoryCalldataMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (appendToHistoryCalldataMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  have hpres := write_read_below_end_from cd (currentLengthMem len)
    payloadStart.toNat len.toNat 64 hlen hsrc (by
      rw [currentLengthMem_size]
      decide)
  rw [appendToHistoryCalldataMem, ← currentLengthMem_size len]
  exact hpres.trans (currentLengthMem_read64 len)

theorem appendToHistoryCalldataMem_size
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (appendToHistoryCalldataMem cd len payloadStart).size = 160 + len.toNat := by
  rw [appendToHistoryCalldataMem]
  have hsize := write_end_size_from cd (currentLengthMem len)
    payloadStart.toNat len.toNat hlen hsrc
  rw [currentLengthMem_size] at hsize
  simpa using hsize

set_option maxHeartbeats 800000 in
theorem appendToHistoryCalldataMem_extract_payload
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (appendToHistoryCalldataMem cd len payloadStart).extract 160 (160 + len.toNat) =
      cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat) := by
  rw [appendToHistoryCalldataMem, ← currentLengthMem_size len]
  exact write_end_extract_tail_from cd (currentLengthMem len)
    payloadStart.toNat len.toNat hlen hsrc

theorem appendToHistoryPaddedMem_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (appendToHistoryPaddedMem cd len payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  rw [appendToHistoryPaddedMem]
  rw [write32_read_below (UInt256.toByteArray (⟨0⟩ : UInt256))
    (appendToHistoryCalldataMem cd len payloadStart)
    (((⟨160⟩ : UInt256) + len).toNat) 128
    (by rw [toByteArray_size])
    (by
      rw [hadd, appendToHistoryCalldataMem_size cd len payloadStart hlen hsrc])
    (by rw [hadd]; omega)]
  exact appendToHistoryCalldataMem_read128 cd len payloadStart hlen hsrc

theorem appendToHistoryPaddedMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (appendToHistoryPaddedMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [appendToHistoryPaddedMem]
  rw [write32_read_below (UInt256.toByteArray (⟨0⟩ : UInt256))
    (appendToHistoryCalldataMem cd len payloadStart)
    (((⟨160⟩ : UInt256) + len).toNat) 64
    (by rw [toByteArray_size])
    (by
      rw [hadd, appendToHistoryCalldataMem_size cd len payloadStart hlen hsrc])
    (by rw [hadd]; omega)]
  exact appendToHistoryCalldataMem_read64 cd len payloadStart hlen hsrc

theorem appendToHistoryDataEnd_toNat_of_short {len : UInt256}
    (hshort : len.toNat < 32) :
    (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat := by
  rw [uadd_toNat]
  rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hle : 160 + len.toNat < 192 := by omega
    exact lt_of_lt_of_le hle (by norm_num [UInt256.size]))

theorem appendToHistoryPaddedMem_size_ge160
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    160 ≤ (appendToHistoryPaddedMem cd len payloadStart).size := by
  rw [appendToHistoryPaddedMem]
  exact le_trans
    (by
      rw [appendToHistoryCalldataMem_size cd len payloadStart hlen hsrc]
      omega)
    (writeWord_size_ge_mem
      (mem := appendToHistoryCalldataMem cd len payloadStart)
      (off := (((⟨160⟩ : UInt256) + len).toNat))
      (word := (⟨0⟩ : UInt256))
      (by rw [hadd, appendToHistoryCalldataMem_size cd len payloadStart hlen hsrc]))

theorem appendToHistoryPaddedMem_size
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (appendToHistoryPaddedMem cd len payloadStart).size = 192 + len.toNat := by
  rw [appendToHistoryPaddedMem]
  have hbase := appendToHistoryCalldataMem_size cd len payloadStart hlen hsrc
  rw [toByteArray_write_eq (⟨0⟩ : UInt256)
    (appendToHistoryCalldataMem cd len payloadStart)
    (((⟨160⟩ : UInt256) + len).toNat)
    (by rw [hadd, hbase])
    (by
      rw [hadd, hbase]
      rw [show 160 + len.toNat - (160 + len.toNat) = 0 by omega]
      exact lt_usize 0 (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, hbase, toByteArray_size, hadd]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (160 + len.toNat - (160 + len.toNat))) =
      ByteArray.empty by
        rw [show 160 + len.toNat - (160 + len.toNat) = 0 by omega]
        exact zeroes_zero (n := USize.ofNat 0) (by rfl),
    ByteArray.size_empty]
  omega

theorem appendToHistoryHistorySlotMem_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (appendToHistoryHistorySlotMem cd len payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  rw [appendToHistoryHistorySlotMem]
  rw [write32_read_above (UInt256.toByteArray (⟨1⟩ : UInt256))
    (appendToHistoryPaddedMem cd len payloadStart) 0 128
    (by rw [toByteArray_size])
    (by exact Nat.zero_le _)
    (by decide)
    (by
      have hge := appendToHistoryPaddedMem_size_ge160 cd len payloadStart hlen hsrc hadd
      omega)]
  exact appendToHistoryPaddedMem_read128 cd len payloadStart hlen hsrc hadd

theorem appendToHistoryHistorySlotMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (appendToHistoryHistorySlotMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr len) := by
  rw [appendToHistoryHistorySlotMem]
  rw [write32_read_above (UInt256.toByteArray (⟨1⟩ : UInt256))
    (appendToHistoryPaddedMem cd len payloadStart) 0 64
    (by rw [toByteArray_size])
    (by exact Nat.zero_le _)
    (by decide)
    (by
      have hge := appendToHistoryPaddedMem_size_ge160 cd len payloadStart hlen hsrc hadd
      omega)]
  exact appendToHistoryPaddedMem_read64 cd len payloadStart hlen hsrc hadd

theorem appendToHistoryHistorySlotMem_size_gt128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    128 < (appendToHistoryHistorySlotMem cd len payloadStart).size := by
  rw [appendToHistoryHistorySlotMem]
  have hbase : 128 < (appendToHistoryPaddedMem cd len payloadStart).size := by
    have hge := appendToHistoryPaddedMem_size_ge160 cd len payloadStart hlen hsrc hadd
    omega
  exact lt_of_lt_of_le hbase
    (writeWord_size_ge_mem
      (mem := appendToHistoryPaddedMem cd len payloadStart)
      (off := 0) (word := (⟨1⟩ : UInt256)) (Nat.zero_le _))

theorem appendToHistoryHistorySlotMem_size_ge192
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    192 ≤ (appendToHistoryHistorySlotMem cd len payloadStart).size := by
  rw [appendToHistoryHistorySlotMem]
  have hbase : 192 ≤ (appendToHistoryPaddedMem cd len payloadStart).size := by
    rw [appendToHistoryPaddedMem_size cd len payloadStart hlen hsrc hadd]
    omega
  exact le_trans hbase
    (writeWord_size_ge_mem
      (mem := appendToHistoryPaddedMem cd len payloadStart)
      (off := 0) (word := (⟨1⟩ : UInt256)) (Nat.zero_le _))

theorem appendToHistoryHelperLoadedLen_of_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat)
    (haw : ¬ (⟨128⟩ : UInt256) ≥ appendToHistoryHelperEntryAw len * ⟨32⟩) :
    appendToHistoryHelperLoadedLen cd len payloadStart = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := appendToHistoryHelperEntryAw len)
    (v := len)
    (by
      have hgt := appendToHistoryHistorySlotMem_size_gt128 cd len payloadStart hlen hsrc hadd
      simpa using hgt)
    haw
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        appendToHistoryHistorySlotMem_read128 cd len payloadStart hlen hsrc hadd)

theorem appendToHistoryHelperEntryAw_eq_7_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    appendToHistoryHelperEntryAw len = ⟨7⟩ := by
  apply u256_inj
  dsimp [appendToHistoryHelperEntryAw, appendToHistoryHistorySlotMemAw]
  simp only [MachineState.M]
  rw [appendToHistoryDataEnd_toNat_of_short hshort]
  have hcopy : (160 + len.toNat + 31) / 32 = 6 := by omega
  have hpad : (160 + len.toNat + 32 + 31) / 32 = 7 := by omega
  rw [hcopy, hpad]
  decide

theorem appendToHistoryHelperEntryAw_mload128_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    ¬ (⟨128⟩ : UInt256) ≥ appendToHistoryHelperEntryAw len * ⟨32⟩ := by
  rw [appendToHistoryHelperEntryAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem appendToHistoryHelperMloadAw_eq_7_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    appendToHistoryHelperMloadAw len = ⟨7⟩ := by
  apply u256_inj
  dsimp [appendToHistoryHelperMloadAw]
  rw [appendToHistoryHelperEntryAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem appendToHistoryHelperMloadAw_mload64_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    ¬ (⟨64⟩ : UInt256) ≥ appendToHistoryHelperMloadAw len * ⟨32⟩ := by
  rw [appendToHistoryHelperMloadAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem appendToHistoryHelperPayloadAw_eq_7_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    appendToHistoryHelperPayloadAw len = ⟨7⟩ := by
  apply u256_inj
  dsimp [appendToHistoryHelperPayloadAw]
  rw [appendToHistoryHelperMloadAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem appendToHistoryHelperPayloadAw_mload64_of_short_nonzero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    ¬ (⟨64⟩ : UInt256) ≥ appendToHistoryHelperPayloadAw len * ⟨32⟩ := by
  rw [appendToHistoryHelperPayloadAw_eq_7_of_short_nonzero hnz hshort]
  decide

theorem appendToHistoryHelperLoadedLen_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    appendToHistoryHelperLoadedLen cd len payloadStart = len := by
  exact appendToHistoryHelperLoadedLen_of_read128 cd len payloadStart hnz hsrc
    (appendToHistoryDataEnd_toNat_of_short hshort)
    (appendToHistoryHelperEntryAw_mload128_of_short_nonzero hnz hshort)

theorem appendToHistoryHelperShortNonemptyConditions_of_abiLen
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    UInt256.gt (appendToHistoryHelperLoadedLen cd len payloadStart)
        ⟨18446744073709551615⟩ = ⟨0⟩ ∧
      UInt256.gt (appendToHistoryHelperLoadedLen cd len payloadStart) ⟨31⟩ = ⟨0⟩ ∧
    (appendToHistoryHelperLoadedLen cd len payloadStart).isZero = ⟨0⟩ := by
  have hloaded := appendToHistoryHelperLoadedLen_short_nonzero
    cd len payloadStart hnz hshort hsrc
  refine ⟨?_, ?_, ?_⟩
  · rw [hloaded]
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
    norm_num [ABI.solcMaxU64]
    omega
  · rw [hloaded]
    apply ugt_zero
    rw [show (⟨31⟩ : UInt256).toNat = 31 from rfl]
    omega
  · rw [hloaded]
    apply isZero_eq_zero_of_ne
    intro hzero
    exact hnz (by rw [hzero]; rfl)

theorem appendToHistoryHistorySlotMem_mload64_short_nonzero
    (cd : ByteArray) (len payloadStart freePtr : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hfree : currentLengthFreePtr len = freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ (appendToHistoryHistorySlotMem cd len payloadStart).size
        ∨ (⟨64⟩ : UInt256) ≥ appendToHistoryHelperMloadAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((appendToHistoryHistorySlotMem cd len payloadStart).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := appendToHistoryHelperMloadAw len)
    (v := freePtr)
    (by
      have hgt := appendToHistoryHistorySlotMem_size_gt128 cd len payloadStart hnz hsrc
        (appendToHistoryDataEnd_toNat_of_short hshort)
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      omega)
    (appendToHistoryHelperMloadAw_mload64_of_short_nonzero hnz hshort)
    (by
      rw [← hfree]
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        appendToHistoryHistorySlotMem_read64 cd len payloadStart hnz hsrc
          (appendToHistoryDataEnd_toNat_of_short hshort))

theorem appendToHistoryPaddedMem_zero_read64 (cd : ByteArray) (payloadStart : UInt256) :
    (appendToHistoryPaddedMem cd ⟨0⟩ payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr ⟨0⟩) := by
  rw [appendToHistoryPaddedMem, appendToHistoryCalldataMem_zero]
  rw [write32_read_below (UInt256.toByteArray (⟨0⟩ : UInt256)) (currentLengthMem ⟨0⟩)
    (((⟨160⟩ : UInt256) + (⟨0⟩ : UInt256)).toNat) 64
    (by rw [toByteArray_size])
    (by rw [currentLengthMem_size]; decide)
    (by decide)]
  exact currentLengthMem_read64 ⟨0⟩

theorem appendToHistoryPaddedMem_zero_read128 (cd : ByteArray) (payloadStart : UInt256) :
    (appendToHistoryPaddedMem cd ⟨0⟩ payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  rw [appendToHistoryPaddedMem, appendToHistoryCalldataMem_zero]
  rw [write32_read_below (UInt256.toByteArray (⟨0⟩ : UInt256)) (currentLengthMem ⟨0⟩)
    (((⟨160⟩ : UInt256) + (⟨0⟩ : UInt256)).toNat) 128
    (by rw [toByteArray_size])
    (by rw [currentLengthMem_size]; decide)
    (by decide)]
  exact currentLengthMem_read128 ⟨0⟩

theorem appendToHistoryPaddedMem_zero_size_ge160 (cd : ByteArray) (payloadStart : UInt256) :
    160 ≤ (appendToHistoryPaddedMem cd ⟨0⟩ payloadStart).size := by
  rw [appendToHistoryPaddedMem, appendToHistoryCalldataMem_zero]
  have h := writeWord_size_ge_mem (mem := currentLengthMem ⟨0⟩)
    (off := (((⟨160⟩ : UInt256) + (⟨0⟩ : UInt256)).toNat))
    (word := (⟨0⟩ : UInt256))
    (by rw [currentLengthMem_size]; decide)
  rwa [currentLengthMem_size] at h

theorem appendToHistoryHistorySlotMem_zero_read64 (cd : ByteArray) (payloadStart : UInt256) :
    (appendToHistoryHistorySlotMem cd ⟨0⟩ payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (currentLengthFreePtr ⟨0⟩) := by
  rw [appendToHistoryHistorySlotMem]
  rw [write32_read_above (UInt256.toByteArray (⟨1⟩ : UInt256))
    (appendToHistoryPaddedMem cd ⟨0⟩ payloadStart) 0 64
    (by rw [toByteArray_size])
    (by exact Nat.zero_le _)
    (by decide)
    (by
      have hge := appendToHistoryPaddedMem_zero_size_ge160 cd payloadStart
      omega)]
  exact appendToHistoryPaddedMem_zero_read64 cd payloadStart

theorem appendToHistoryHistorySlotMem_zero_read128 (cd : ByteArray) (payloadStart : UInt256) :
    (appendToHistoryHistorySlotMem cd ⟨0⟩ payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  rw [appendToHistoryHistorySlotMem]
  rw [write32_read_above (UInt256.toByteArray (⟨1⟩ : UInt256))
    (appendToHistoryPaddedMem cd ⟨0⟩ payloadStart) 0 128
    (by rw [toByteArray_size])
    (by exact Nat.zero_le _)
    (by decide)
    (by
      have hge := appendToHistoryPaddedMem_zero_size_ge160 cd payloadStart
      omega)]
  exact appendToHistoryPaddedMem_zero_read128 cd payloadStart

theorem appendToHistoryHistorySlotMem_zero_size_gt64 (cd : ByteArray) (payloadStart : UInt256) :
    64 < (appendToHistoryHistorySlotMem cd ⟨0⟩ payloadStart).size := by
  rw [appendToHistoryHistorySlotMem]
  have hbase : 64 < (appendToHistoryPaddedMem cd ⟨0⟩ payloadStart).size := by
    have hge := appendToHistoryPaddedMem_zero_size_ge160 cd payloadStart
    omega
  exact writeWord_size_gt64_of_mem (mem := appendToHistoryPaddedMem cd ⟨0⟩ payloadStart)
    (off := 0) (word := (⟨1⟩ : UInt256)) hbase (Nat.zero_le _)

theorem appendToHistoryHistorySlotMem_zero_size_ge160 (cd : ByteArray) (payloadStart : UInt256) :
    160 ≤ (appendToHistoryHistorySlotMem cd ⟨0⟩ payloadStart).size := by
  rw [appendToHistoryHistorySlotMem]
  exact le_trans (appendToHistoryPaddedMem_zero_size_ge160 cd payloadStart)
    (writeWord_size_ge_mem
      (mem := appendToHistoryPaddedMem cd ⟨0⟩ payloadStart)
      (off := 0) (word := (⟨1⟩ : UInt256)) (Nat.zero_le _))

theorem appendToHistoryHistorySlotMem_zero_mload64 (cd : ByteArray) (payloadStart : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (appendToHistoryHistorySlotMem cd ⟨0⟩ payloadStart).size
        ∨ (⟨64⟩ : UInt256) ≥ appendToHistoryHelperMloadAw ⟨0⟩ * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((appendToHistoryHistorySlotMem cd ⟨0⟩ payloadStart).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      currentLengthFreePtr ⟨0⟩ := by
  exact currentLength_mload64_of_read64
    (mem := appendToHistoryHistorySlotMem cd ⟨0⟩ payloadStart)
    (aw := appendToHistoryHelperMloadAw ⟨0⟩)
    (freePtr := currentLengthFreePtr ⟨0⟩)
    (appendToHistoryHistorySlotMem_zero_size_gt64 cd payloadStart)
    (by native_decide)
    (appendToHistoryHistorySlotMem_zero_read64 cd payloadStart)

theorem appendToHistoryHelperLoadedLen_zero
    (cd : ByteArray) (payloadStart : UInt256) :
    appendToHistoryHelperLoadedLen cd ⟨0⟩ payloadStart = ⟨0⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := appendToHistoryHelperEntryAw ⟨0⟩)
    (v := (⟨0⟩ : UInt256))
    (by
      have hge := appendToHistoryHistorySlotMem_zero_size_ge160 cd payloadStart
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      omega)
    (by native_decide)
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        appendToHistoryHistorySlotMem_zero_read128 cd payloadStart)

theorem appendToHistoryArrayDataBase_eq
    (cd : ByteArray) (len payloadStart : UInt256) :
    appendToHistoryArrayDataBase cd len payloadStart = bytesLikeDataBase ⟨1⟩ := by
  rw [appendToHistoryArrayDataBase, appendToHistoryHistorySlotMem_read0]
  simpa [bytesLikeDataBase] using keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))

theorem u256_add_one_sub_one (w : UInt256) :
    (w + ⟨1⟩ : UInt256) - ⟨1⟩ = w := by
  apply u256_inj
  change (UInt256.sub (w + ⟨1⟩) ⟨1⟩).toNat = w.toNat
  by_cases hfit : w.toNat + 1 < UInt256.size
  · have hadd : (w + ⟨1⟩ : UInt256).toNat = w.toNat + 1 := by
      rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt hfit
    rw [usub_toNat (a := w + ⟨1⟩) (b := (⟨1⟩ : UInt256))
      (by rw [hadd, show (⟨1⟩ : UInt256).toNat = 1 from rfl]; omega)]
    rw [hadd, show (⟨1⟩ : UInt256).toNat = 1 from rfl]
    omega
  · have hwrap : w.toNat + 1 = UInt256.size := by
      have hle : w.toNat + 1 ≤ UInt256.size := by
        exact Nat.succ_le_of_lt w.val.isLt
      omega
    have hadd : (w + ⟨1⟩ : UInt256).toNat = 0 := by
      rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 from rfl, hwrap, Nat.mod_self]
    rw [usub_toNat_underflow (a := w + ⟨1⟩) (b := (⟨1⟩ : UInt256))
      (by rw [hadd, show (⟨1⟩ : UInt256).toNat = 1 from rfl]; omega)]
    rw [hadd, show (⟨1⟩ : UInt256).toNat = 1 from rfl]
    omega

/-- `wordOfInt (Int.ofNat a.toNat) = a` for an EVM word. -/
theorem stringStoreWordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

theorem appendToHistoryNewElementSlot_eq_historyElemBase
    (σ : AccountMap) (I : ExecutionEnv) (cd : ByteArray) (len payloadStart : UInt256) :
    appendToHistoryNewElementSlot σ I cd len payloadStart =
      historyElemBase
        (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat)) := by
  rw [appendToHistoryNewElementSlot, appendToHistoryArrayDataBase_eq,
    appendToHistoryFirstStorageValue, u256_add_one_sub_one, historyElemBase,
    keyValueToWord, stringStoreWordOfInt_ofNat_toNat]
  rw [u256_ofNat_toNat]

/-- Storing a full-slot StringStore `uint256` writes exactly the EVM word in the same slot. -/
theorem stringStoreStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, stringStoreWordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = val.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem stringStoreWordOfInt_succ (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat + 1) = w + ⟨1⟩ := by
  have hn : ¬ Int.ofNat w.toNat + 1 < 0 := by
    exact not_lt_of_ge
      (Int.add_nonneg (Int.natCast_nonneg (w.toNat)) (show (0 : Int) ≤ 1 by decide))
  rw [EVM.wordOfInt, if_neg hn]
  apply u256_inj
  show ((Fin.ofNat UInt256.size (Int.toNat (Int.ofNat w.toNat + 1))).val : Nat) =
    ((w + ⟨1⟩ : UInt256).val.val : Nat)
  have hto : (Int.ofNat w.toNat + 1).toNat = w.toNat + 1 := by
    have hcast : (((Int.ofNat w.toNat + 1).toNat : Nat) : Int) =
        (w.toNat + 1 : Nat) := by
      rw [Int.toNat_of_nonneg (not_lt.mp hn)]
      norm_num
    omega
  rw [hto, Fin.val_ofNat]
  change (w.toNat + 1) % UInt256.size = (w + ⟨1⟩).toNat
  rw [uadd_toNat]
  rw [show ({ val := 1 } : UInt256).toNat = 1 by rfl]

/-- Storing a full-slot StringStore `uint256` successor writes the same wrapping EVM word as ADD. -/
theorem stringStoreStorageLocStore_uint256_succ
    (evm : EVM.State) (slot old : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat old.toNat + 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (old + ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, stringStoreWordOfInt_succ, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (old + ⟨1⟩)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (old + ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem appendToHistoryFirstStorageLoaded_eq_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    appendToHistoryFirstStorageLoaded σ I =
      appendToHistoryFirstStorageLoaded τ I := by
  exact accountMapEquiv_storage_findD hAccounts I.codeOwner
    appendToHistoryFirstStorageSlot ⟨0⟩

theorem appendToHistoryFirstStorageValue_eq_of_accountMapEquiv
    {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    appendToHistoryFirstStorageValue σ I =
      appendToHistoryFirstStorageValue τ I := by
  simp [appendToHistoryFirstStorageValue,
    appendToHistoryFirstStorageLoaded_eq_of_accountMapEquiv hAccounts]

theorem appendToHistoryFirstStorageMap_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (appendToHistoryFirstStorageMap σ_evm I)
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner appendToHistoryFirstStorageSlot
        (appendToHistoryFirstStorageValue σ_solm I)).accountMap := by
  rw [storageStore_accountMap]
  simp only [initState]
  have hval := appendToHistoryFirstStorageValue_eq_of_accountMapEquiv
    (I := I) hAccounts
  rw [← hval]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner appendToHistoryFirstStorageSlot
    (appendToHistoryFirstStorageValue σ_evm I) hAccounts

theorem appendToHistoryFirstStorageCreatedAccounts
    {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
      I.codeOwner appendToHistoryFirstStorageSlot
      (appendToHistoryFirstStorageValue σ_solm I)).createdAccounts = cA := by
  simp [storageStore_createdAccounts, initState]

theorem appendToHistoryHistoryLengthLoad_init
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    storageLocLoad (initState cA gh bl σ σ₀ g A I)
      (uint256Loc appendToHistoryFirstStorageSlot) =
      .int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat) := by
  simpa [appendToHistoryFirstStorageLoaded, appendToHistoryFirstStorageSlot, initState]
    using stringStoreStorageLocLoad_uint256
      (initState cA gh bl σ σ₀ g A I) appendToHistoryFirstStorageSlot

theorem appendToHistoryHistoryLengthStore_init
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    storageLocStore (initState cA gh bl σ σ₀ g A I)
      (uint256Loc appendToHistoryFirstStorageSlot)
      (.int (((appendToHistoryFirstStorageLoaded σ I).toNat : Int) + 1)) =
      some (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
        I.codeOwner appendToHistoryFirstStorageSlot
        (appendToHistoryFirstStorageValue σ I)) := by
  simpa [appendToHistoryFirstStorageValue, initState]
    using stringStoreStorageLocStore_uint256_succ
      (initState cA gh bl σ σ₀ g A I) appendToHistoryFirstStorageSlot
      (appendToHistoryFirstStorageLoaded σ I)

theorem appendToHistoryPushArray_afterLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {suffix : ByteArray} :
    pushArray? stringStoreConfig
      { contract := stringStoreContract
        locals := (∅ : Store).insert "suffix" (.bytes suffix) }
      (initState cA gh bl σ σ₀ g A I) historyRef (some (.bytes suffix)) =
      writeStorage? stringStoreConfig
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner appendToHistoryFirstStorageSlot
          (appendToHistoryFirstStorageValue σ I))
        { base := "history",
          steps := [.aindex (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat))] }
        .string (.bytes suffix) := by
  simp [pushArray?, resolveDynamicArrayRef?, resolveStorageRef?, evalStorageRef,
    evalStorageRefSteps, historyRef, storageTypeAt?, stringStoreConfig, stringStoreContract,
    storageDecls, stringSt, stringStoreStorageLayout, stringStoreLayout,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  change
    (match storageLocLoad (initState cA gh bl σ σ₀ g A I)
        (uint256Loc appendToHistoryFirstStorageSlot) with
      | .int len =>
          match
            (match storageLocStore (initState cA gh bl σ σ₀ g A I)
              (uint256Loc appendToHistoryFirstStorageSlot) (.int (len + 1)) with
            | some a => EvalResult.ok a
            | none => EvalResult.error EvalError.storageError) with
          | .ok evmLen =>
              writeStorage?
                { storage := stringStoreStorageLayout
                  externalABI := defaultExternalCallABI
                  selfDeployment := genSolidityConstructorDeployment [] }
                evmLen { base := "history", steps := [.aindex (.int len)] }
                .string (.bytes suffix)
          | .revert => EvalResult.revert
          | .error e => EvalResult.error e
      | _ => EvalResult.error EvalError.storageError) =
      writeStorage? stringStoreConfig
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner appendToHistoryFirstStorageSlot
          (appendToHistoryFirstStorageValue σ I))
        { base := "history",
          steps := [.aindex (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat))] }
        .string (.bytes suffix)
  rw [appendToHistoryHistoryLengthLoad_init]
  simp
  rw [appendToHistoryHistoryLengthStore_init]
  simp [stringStoreConfig, stringStoreContract]

theorem appendToHistory_solidifyDecodeBytesLengthHeader_zero :
    solidityDecodeBytesLengthHeader ⟨0⟩ = .ok 0 := by
  have hflag : UInt256.land (⟨0⟩ : UInt256) ⟨1⟩ = ⟨0⟩ := by rfl
  have hraw : UInt256.div (⟨0⟩ : UInt256) ⟨2⟩ = ⟨0⟩ := by rfl
  have hmask : UInt256.land (⟨0⟩ : UInt256) ⟨127⟩ = ⟨0⟩ := by rfl
  have hvalidFinal : UInt256.sub (⟨0⟩ : UInt256)
      (UInt256.lt (⟨0⟩ : UInt256) ⟨32⟩) ≠ ⟨0⟩ := by
    decide
  simp [solidityDecodeBytesLengthHeader, hflag, hraw, hmask, hvalidFinal]

theorem appendToHistory_empty_readWithPadding_word_zero :
    uInt256OfByteArray (ByteArray.empty.readWithPadding 0 32) = (⟨0⟩ : UInt256) := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  simp [byteArray_zeroes_toList, uInt256OfByteArray, fromBytes'_replicate_zero]
  rfl

theorem appendToHistoryWriteStorage_empty_afterLength
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hload :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner appendToHistoryFirstStorageSlot
          (appendToHistoryFirstStorageValue σ I))
        I.codeOwner
        (historyElemBase
          (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat))) =
        ⟨0⟩) :
    writeStorage? stringStoreConfig
      (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
        I.codeOwner appendToHistoryFirstStorageSlot
        (appendToHistoryFirstStorageValue σ I))
      { base := "history",
        steps := [.aindex (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat))] }
      .string (.bytes ByteArray.empty) =
      .ok
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
            I.codeOwner appendToHistoryFirstStorageSlot
            (appendToHistoryFirstStorageValue σ I))
          I.codeOwner
          (historyElemBase
            (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat)))
          ⟨0⟩) := by
  have howner :
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hloadCast :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner appendToHistoryFirstStorageSlot
          (appendToHistoryFirstStorageValue σ I))
        I.codeOwner
        (historyElemBase
          (.int (((appendToHistoryFirstStorageLoaded σ I).toNat : Nat) : Int))) =
        ⟨0⟩ := by
    simpa using hload
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    appendToHistory_solidifyDecodeBytesLengthHeader_zero
  simp [writeStorage?, writeStorageBytesLike?, storagePrepareResultToEval,
    stringStoreConfig, stringStoreStorageLayout, solidityWriteBytes?, solidityShortBytesWord,
    solidityBytesBaseSlotAndLength?, stringStoreLayout, bytesLikeLengthLoc, checkBytesPacked,
    storageStore_executionEnv, howner, hloadCast, hdecode]
  rw [appendToHistory_empty_readWithPadding_word_zero]
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
  rw [show UInt256.lor (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ by rfl]

theorem appendToHistoryWriteStorage_short_afterLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {suffix : ByteArray}
    (hshort : suffix.size < 32)
    (hload :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner appendToHistoryFirstStorageSlot
          (appendToHistoryFirstStorageValue σ I))
        I.codeOwner
        (historyElemBase
          (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat))) =
        ⟨0⟩) :
    writeStorage? stringStoreConfig
      (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
        I.codeOwner appendToHistoryFirstStorageSlot
        (appendToHistoryFirstStorageValue σ I))
      { base := "history",
        steps := [.aindex (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat))] }
      .string (.bytes suffix) =
      .ok
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
            I.codeOwner appendToHistoryFirstStorageSlot
            (appendToHistoryFirstStorageValue σ I))
          I.codeOwner
          (historyElemBase
            (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat)))
          (solidityShortBytesWord suffix)) := by
  have howner :
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hloadCast :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner appendToHistoryFirstStorageSlot
          (appendToHistoryFirstStorageValue σ I))
        I.codeOwner
        (historyElemBase
          (.int (((appendToHistoryFirstStorageLoaded σ I).toNat : Nat) : Int))) =
        ⟨0⟩ := by
    simpa using hload
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    appendToHistory_solidifyDecodeBytesLengthHeader_zero
  simp [writeStorage?, writeStorageBytesLike?, storagePrepareResultToEval,
    stringStoreConfig, stringStoreStorageLayout, solidityWriteBytes?, solidityShortBytesWord,
    solidityBytesBaseSlotAndLength?, stringStoreLayout, bytesLikeLengthLoc, checkBytesPacked,
    storageStore_executionEnv, howner, hloadCast, hdecode, hshort]

theorem appendToHistory_empty_afterLength_load_of_existingHeader_zero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hzero :
      appendToHistoryExistingElementHeader σ_evm I cd len payloadStart = ⟨0⟩) :
    Solm.EVM.storageLoad
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner appendToHistoryFirstStorageSlot
        (appendToHistoryFirstStorageValue σ_solm I))
      I.codeOwner
      (historyElemBase
        (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ_solm I).toNat))) =
      ⟨0⟩ := by
  let elemSlot :=
    historyElemBase (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ_solm I).toNat))
  have hslot :
      appendToHistoryNewElementSlot σ_evm I cd len payloadStart = elemSlot := by
    rw [appendToHistoryNewElementSlot_eq_historyElemBase]
    rw [appendToHistoryFirstStorageLoaded_eq_of_accountMapEquiv hAccounts]
  have hleft :
      ((appendToHistoryFirstStorageMap σ_evm I).find? I.codeOwner).option
          (⟨0⟩ : UInt256) (fun acc => acc.storage.findD elemSlot ⟨0⟩) =
        ⟨0⟩ := by
    simpa [appendToHistoryExistingElementHeader, elemSlot, hslot] using hzero
  have hEquiv :=
    appendToHistoryFirstStorageMap_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hAccounts
  have hfind := accountMapEquiv_storage_findD hEquiv I.codeOwner elemSlot (⟨0⟩ : UInt256)
  have hright :
      (((Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          I.codeOwner appendToHistoryFirstStorageSlot
          (appendToHistoryFirstStorageValue σ_solm I)).accountMap.find? I.codeOwner).option
          (⟨0⟩ : UInt256) (fun acc => acc.storage.findD elemSlot ⟨0⟩)) =
        ⟨0⟩ := by
    exact hfind ▸ hleft
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, elemSlot]
    using hright

theorem appendToHistoryPushArray_empty_of_existingHeader_zero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hzero :
      appendToHistoryExistingElementHeader σ_evm I cd len payloadStart = ⟨0⟩) :
    pushArray? stringStoreConfig
      { contract := stringStoreContract
        locals := (∅ : Store).insert "suffix" (.bytes ByteArray.empty) }
      (initState cA gh bl σ_solm σ₀ g A I) historyRef (some (.bytes ByteArray.empty)) =
      .ok
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
            I.codeOwner appendToHistoryFirstStorageSlot
            (appendToHistoryFirstStorageValue σ_solm I))
          I.codeOwner
          (historyElemBase
            (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ_solm I).toNat)))
          ⟨0⟩) := by
  rw [appendToHistoryPushArray_afterLength]
  exact appendToHistoryWriteStorage_empty_afterLength
    (hload := appendToHistory_empty_afterLength_load_of_existingHeader_zero
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) cd len payloadStart hAccounts hzero)

noncomputable def appendToHistorySolmEmptyFinalState
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : Sat256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
      I.codeOwner appendToHistoryFirstStorageSlot
      (appendToHistoryFirstStorageValue σ I))
    I.codeOwner
    (historyElemBase
      (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat)))
    ⟨0⟩

noncomputable def appendToHistorySolmShortFinalState
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : Sat256)
    (header : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
      I.codeOwner appendToHistoryFirstStorageSlot
      (appendToHistoryFirstStorageValue σ I))
    I.codeOwner
    (historyElemBase
      (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ I).toNat)))
    header

theorem appendToHistoryPushArray_short_of_existingHeader_zero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd suffix : ByteArray) (len payloadStart : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : suffix.size < 32)
    (hzero :
      appendToHistoryExistingElementHeader σ_evm I cd len payloadStart = ⟨0⟩) :
    pushArray? stringStoreConfig
      { contract := stringStoreContract
        locals := (∅ : Store).insert "suffix" (.bytes suffix) }
      (initState cA gh bl σ_solm σ₀ g A I) historyRef (some (.bytes suffix)) =
      .ok
        (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g
          (solidityShortBytesWord suffix)) := by
  rw [appendToHistoryPushArray_afterLength]
  exact appendToHistoryWriteStorage_short_afterLength
    (hshort := hshort)
    (hload := appendToHistory_empty_afterLength_load_of_existingHeader_zero
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) cd len payloadStart hAccounts hzero)

theorem appendToHistorySolmEmptyFinalState_createdAccounts
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    (appendToHistorySolmEmptyFinalState cA gh bl σ σ₀ A I g).createdAccounts = cA := by
  simp [appendToHistorySolmEmptyFinalState, storageStore_createdAccounts, initState]

theorem appendToHistorySolmShortFinalState_createdAccounts
    {cA gh bl σ σ₀ A I} {g : Sat256} {header : UInt256} :
    (appendToHistorySolmShortFinalState cA gh bl σ σ₀ A I g header).createdAccounts = cA := by
  simp [appendToHistorySolmShortFinalState, storageStore_createdAccounts, initState]

theorem appendToHistorySolmEmptyFinalState_eq_short
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    appendToHistorySolmEmptyFinalState cA gh bl σ σ₀ A I g =
      appendToHistorySolmShortFinalState cA gh bl σ σ₀ A I g ⟨0⟩ := by
  rfl

theorem appendToHistoryShortFinal_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart header : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (appendToHistoryShortElementWriteMap σ_evm I cd len payloadStart header)
      (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header).accountMap := by
  have hslot :
      appendToHistoryNewElementSlot σ_evm I cd len payloadStart =
        historyElemBase
          (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ_solm I).toNat)) := by
    rw [appendToHistoryNewElementSlot_eq_historyElemBase]
    rw [appendToHistoryFirstStorageLoaded_eq_of_accountMapEquiv hAccounts]
  have hfirst :=
    appendToHistoryFirstStorageMap_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hAccounts
  unfold appendToHistoryShortElementWriteMap appendToHistorySolmShortFinalState
  rw [hslot, storageStore_accountMap]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner
    (historyElemBase
      (.int (Int.ofNat (appendToHistoryFirstStorageLoaded σ_solm I).toNat)))
    header hfirst

theorem appendToHistoryShortEmptyFinal_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (appendToHistoryShortElementWriteMap σ_evm I cd len payloadStart ⟨0⟩)
      (appendToHistorySolmEmptyFinalState cA gh bl σ_solm σ₀ A I g).accountMap := by
  simpa [appendToHistorySolmEmptyFinalState_eq_short] using
    appendToHistoryShortFinal_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      cd len payloadStart ⟨0⟩ hAccounts

theorem appendToHistorySolmShortFinal_historyLengthLoad
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart header : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad
      (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header)
      (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header).executionEnv.codeOwner
      appendToHistoryFirstStorageSlot =
      appendToHistoryShortReturnLength σ_evm I cd len payloadStart header := by
  have hFinal :=
    appendToHistoryShortFinal_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) cd len payloadStart header hAccounts
  have hfind := accountMapEquiv_storage_findD hFinal I.codeOwner
    appendToHistoryFirstStorageSlot (⟨0⟩ : UInt256)
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    appendToHistoryShortReturnLength, appendToHistorySolmShortFinalState,
    storageStore_executionEnv] using hfind.symm

theorem appendToHistorySolmEmptyFinal_historyLengthLoad
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad
      (appendToHistorySolmEmptyFinalState cA gh bl σ_solm σ₀ A I g)
      (appendToHistorySolmEmptyFinalState cA gh bl σ_solm σ₀ A I g).executionEnv.codeOwner
      appendToHistoryFirstStorageSlot =
      appendToHistoryShortReturnLength σ_evm I cd len payloadStart ⟨0⟩ := by
  simpa [appendToHistorySolmEmptyFinalState_eq_short] using
    appendToHistorySolmShortFinal_historyLengthLoad
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) cd len payloadStart ⟨0⟩ hAccounts

theorem appendToHistoryReturnLengthEval_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd suffix : ByteArray) (len payloadStart header : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    evalExpr? stringStoreConfig
      { contract := stringStoreContract
        locals := (∅ : Store).insert "suffix" (.bytes suffix) }
      (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header)
      (.arrayLength .storage historyRef) =
      .ok (.int (Int.ofNat
        (appendToHistoryShortReturnLength σ_evm I cd len payloadStart header).toNat)) := by
  let evm' := appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header
  have hload :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
        appendToHistoryFirstStorageSlot =
      appendToHistoryShortReturnLength σ_evm I cd len payloadStart header :=
    appendToHistorySolmShortFinal_historyLengthLoad
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) cd len payloadStart header hAccounts
  have hlen :
      storageLocLoad evm' (uint256Loc appendToHistoryFirstStorageSlot) =
        .int (Int.ofNat
          (appendToHistoryShortReturnLength σ_evm I cd len payloadStart header).toNat) := by
    have hbase := stringStoreStorageLocLoad_uint256 evm' appendToHistoryFirstStorageSlot
    rw [hload] at hbase
    exact hbase
  simp [evalExpr?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, historyRef,
    readStorageArrayLength?, storageTypeAt?, stringStoreConfig, stringStoreContract,
    storageDecls, stringSt, stringStoreStorageLayout, stringStoreLayout,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show storageLocLoad
      (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header)
      (uint256Loc ⟨1⟩) =
        .int (Int.ofNat
          (appendToHistoryShortReturnLength σ_evm I cd len payloadStart header).toNat) by
    simpa [evm', appendToHistoryFirstStorageSlot] using hlen]
  rfl

theorem appendToHistoryReturnLengthEval_empty
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    evalExpr? stringStoreConfig
      { contract := stringStoreContract
        locals := (∅ : Store).insert "suffix" (.bytes ByteArray.empty) }
      (appendToHistorySolmEmptyFinalState cA gh bl σ_solm σ₀ A I g)
      (.arrayLength .storage historyRef) =
      .ok (.int (Int.ofNat
        (appendToHistoryShortReturnLength σ_evm I cd len payloadStart ⟨0⟩).toNat)) := by
  simpa [appendToHistorySolmEmptyFinalState_eq_short] using
    appendToHistoryReturnLengthEval_short
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      cd ByteArray.empty len payloadStart ⟨0⟩ hAccounts

theorem stringStoreX_appendToHistoryFirstStorageWrite {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1832⟩
      [⟨128⟩, ⟨0⟩, len, payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryPaddedMem I.calldata len payloadStart)
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
          (((⟨160⟩ : UInt256) + len).toNat) 32))
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1845⟩
        [appendToHistoryFirstStorageValue σ I, appendToHistoryFirstStorageSlot,
          ⟨1⟩, ⟨128⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryPaddedMem I.calldata len payloadStart)
        (UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
            (((⟨160⟩ : UInt256) + len).toNat) 32))
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd1840 := evm_run rd with [
    push1 ⟨1⟩, dup2, swap1, dup1, push1 ⟨1⟩, dup2]
  obtain ⟨_, _, rd1841⟩ := rd1840.sload (by native_decide) (by evm_ov)
  have rd1844 := evm_run rd1841 with [add, dup1, dup3]
  obtain ⟨_, _, rd1845⟩ := rd1844.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [appendToHistoryFirstStorageSlot, appendToHistoryFirstStorageLoaded,
      appendToHistoryFirstStorageValue, appendToHistoryFirstStorageMap] using rd1845⟩

theorem stringStoreX_appendToHistoryReachStringWriteHelper {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1845⟩
      [appendToHistoryFirstStorageValue σ I, appendToHistoryFirstStorageSlot,
        ⟨1⟩, ⟨128⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryPaddedMem I.calldata len payloadStart)
      (UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
          (((⟨160⟩ : UInt256) + len).toNat) 32))
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
        [appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperEntryAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd1855 := evm_run rd with [
    dup1, swap2, pop, pop, push1 ⟨1⟩, swap1, sub, swap1, push0]
  let aw0 : UInt256 :=
    UInt256.ofNat
      (MachineState.M
        (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat)).toNat
        (((⟨160⟩ : UInt256) + len).toNat) 32)
  have rd1856 := RD.mstore
    (Cₘ (appendToHistoryHistorySlotMemAw len) - Cₘ aw0)
    (appendToHistoryHistorySlotMem I.calldata len payloadStart)
    (appendToHistoryHistorySlotMemAw len)
    rd1855 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw0,
        appendToHistoryHistorySlotMemAw])
    (by rfl)
    (by
      simp [appendToHistoryHistorySlotMemAw])
    (by evm_ov)
  have rd1859 := evm_run rd1856 with [push1 ⟨32⟩, push0]
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by native_decide
  have rd1860 := RD.keccak256
    (Cₘ (UInt256.ofNat (MachineState.M (appendToHistoryHistorySlotMemAw len).toNat 0 32)) -
      Cₘ (appendToHistoryHistorySlotMemAw len))
    (appendToHistoryArrayDataBase I.calldata len payloadStart)
    (UInt256.ofNat (MachineState.M (appendToHistoryHistorySlotMemAw len).toNat 0 32))
    rd1859 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        appendToHistoryHistorySlotMemAw, h32])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd3715 := evm_run rd1860 with [
    add, push0, swap1, swap2, swap1, swap2, swap1, swap2, pop, swap1, dup2,
    push2 ⟨1880⟩, swap2, swap1, push2 ⟨3715⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [appendToHistoryFirstStorageSlot, appendToHistoryFirstStorageLoaded,
      appendToHistoryFirstStorageValue, appendToHistoryFirstStorageMap,
      appendToHistoryArrayDataBase, appendToHistoryNewElementSlot,
      appendToHistoryHelperEntryAw, aw0] using rd3715⟩

theorem stringStoreX_appendToHistoryReadHelperMemoryLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      [appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperEntryAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3724⟩
        [appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd2551 := evm_run rd with [
    jumpdest, push2 ⟨3724⟩, dup3, push2 ⟨2548⟩, jump (by jump_dest),
    jumpdest, push0, dup2]
  have h128 : (⟨128⟩ : UInt256).toNat = 128 := by native_decide
  have rd2552 := RD.mload
    (Cₘ (appendToHistoryHelperMloadAw len) - Cₘ (appendToHistoryHelperEntryAw len))
    (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
    (appendToHistoryHelperMloadAw len)
    rd2551 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        appendToHistoryHelperEntryAw, appendToHistoryHelperMloadAw, h128])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd3724 := evm_run rd2552 with [
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [appendToHistoryHelperLoadedLen, appendToHistoryHelperMloadAw] using rd3724⟩

theorem stringStoreX_appendToHistoryHelperLengthBoundOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart ret : UInt256} {k C : Nat}
    (hlenOk :
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3724⟩
      [appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3749⟩
        [appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3725 := evm_run rd with [jumpdest]
  have rd3734 := RD.pushConst rd3725 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3740 := evm_run rd3734 with [
    dup2, gt, iszero, push2 ⟨3749⟩]
  have rd3749 := RD.jumpiT rd3740 (by native_decide)
    (by rw [hlenOk]; decide)
    (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, by simpa using rd3749⟩

theorem stringStoreX_appendToHistoryLoadExistingElementHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3749⟩
      [appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
        [appendToHistoryExistingElementHeader σ I I.calldata len payloadStart, ⟨3759⟩,
          appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3754 := evm_run rd with [jumpdest, push2 ⟨3759⟩, dup3]
  obtain ⟨_, _, rd3755⟩ := rd3754.sload (by native_decide) (by evm_ov)
  have rd3189 := evm_run rd3755 with [push2 ⟨3189⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [appendToHistoryExistingElementHeader] using rd3189⟩

theorem stringStoreX_appendToHistoryDecodeExistingHeaderZero {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hheader :
      appendToHistoryExistingElementHeader σ I I.calldata len payloadStart = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3189⟩
      [appendToHistoryExistingElementHeader σ I I.calldata len payloadStart, ⟨3759⟩,
        appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3759⟩
        [⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3206 := evm_run rd with [
    jumpdest, push0, push1 ⟨2⟩, dup3, div, swap1, pop, push1 ⟨1⟩, dup3, and, dup1,
    push2 ⟨3212⟩, jumpiNT (by rw [hheader]; decide)]
  have rd3222 := evm_run rd3206 with [
    push1 ⟨127⟩, dup3, and, swap2, pop, jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub,
    push2 ⟨3231⟩]
  have rd3231 := RD.jumpiT rd3222 (by native_decide)
    (by rw [hheader]; decide)
    (by jump_dest)
    (by evm_ov)
  have rd3759 := evm_run rd3231 with [
    jumpdest, pop, swap2, swap1, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [hheader] using rd3759⟩

theorem stringStoreX_appendToHistorySkipClearOldZero {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3759⟩
      [⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3770⟩
        [⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3574 := evm_run rd with [
    jumpdest, push2 ⟨3770⟩, dup3, dup3, dup6, push2 ⟨3565⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨3643⟩]
  have rd3643 := RD.jumpiT rd3574 (by native_decide)
    (by decide)
    (by jump_dest)
    (by evm_ov)
  have rd3770 := evm_run rd3643 with [
    jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd3770⟩

theorem stringStoreX_appendToHistoryNewValueShortBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hshort :
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart) ⟨31⟩ = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3770⟩
      [⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3788⟩
        [⟨0⟩, ⟨32⟩, ⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3787 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, swap1, pop, push1 ⟨31⟩, dup4, gt, push1 ⟨1⟩,
    dup2, eq, push2 ⟨3819⟩]
  have rd3788 := RD.jumpiNT rd3787 (by native_decide)
    (by rw [hshort]; decide)
    (by evm_ov)
  exact ⟨_, _, by simpa [hshort] using rd3788⟩

theorem stringStoreX_appendToHistoryNewValueShortEmptyPacked {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hzero :
      appendToHistoryHelperLoadedLen I.calldata len payloadStart = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3788⟩
      [⟨0⟩, ⟨32⟩, ⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3811⟩
        [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨32⟩, ⟨0⟩, ⟨0⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3794 := evm_run rd with [
    push0, dup5, iszero, push2 ⟨3801⟩]
  have rd3801 := RD.jumpiT rd3794 (by native_decide)
    (by rw [hzero]; decide)
    (by jump_dest)
    (by evm_ov)
  have rd3688 := evm_run rd3801 with [
    jumpdest, push2 ⟨3811⟩, dup6, dup3, push2 ⟨3688⟩, jump (by jump_dest)]
  have rd3811 := evm_run rd3688 with [
    jumpdest, push0, push2 ⟨3699⟩, dup4, dup4, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, push0, push2 ⟨3675⟩, push0, not, dup5, push1 ⟨8⟩, mul,
    push2 ⟨3648⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shr, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, not, dup1, dup4, and, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, swap2, pop, dup3, push1 ⟨2⟩, mul, dup3, or, swap1, pop,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [hzero] using rd3811⟩

theorem stringStoreX_appendToHistoryNewValueShortPayloadLoaded {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hnonzero :
      (appendToHistoryHelperLoadedLen I.calldata len payloadStart).isZero = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3788⟩
      [⟨0⟩, ⟨32⟩, ⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3801⟩
        [appendToHistoryHelperPayloadWord I.calldata len payloadStart, ⟨0⟩, ⟨32⟩, ⟨0⟩,
          appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperPayloadAw len)
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3794 := evm_run rd with [
    push0, dup5, iszero, push2 ⟨3801⟩]
  have rd3795 := RD.jumpiNT rd3794 (by native_decide)
    (by rw [hnonzero])
    (by evm_ov)
  have rd3798 := evm_run rd3795 with [dup3, dup8, add]
  have haddrWord : ((⟨128⟩ : UInt256) + ⟨32⟩) = ⟨160⟩ := by native_decide
  have haddr : (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) = 160 := by native_decide
  have rd3799 := RD.mload
    (Cₘ (appendToHistoryHelperPayloadAw len) - Cₘ (appendToHistoryHelperMloadAw len))
    (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
    (appendToHistoryHelperPayloadAw len)
    rd3798 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        appendToHistoryHelperPayloadAw, haddr])
    (by simp [appendToHistoryHelperPayloadWord, haddrWord])
    (by simp [appendToHistoryHelperPayloadAw, haddr])
    (by evm_ov)
  have rd3801 := evm_run rd3799 with [swap1, pop]
  exact ⟨_, _, by
    simpa [appendToHistoryHelperPayloadWord, appendToHistoryHelperPayloadAw, haddr] using rd3801⟩

theorem stringStoreX_appendToHistoryNewValueShortPayloadPacked {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret payloadWord aw : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3801⟩
      [payloadWord, ⟨0⟩, ⟨32⟩, ⟨0⟩,
        appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      aw
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3811⟩
        [appendToHistoryShortPackedHeader payloadWord
            (appendToHistoryHelperLoadedLen I.calldata len payloadStart),
          payloadWord, ⟨0⟩, ⟨32⟩, ⟨0⟩,
          appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        aw
        ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k' C' := by
  have rd3688 := evm_run rd with [
    jumpdest, push2 ⟨3811⟩, dup6, dup3, push2 ⟨3688⟩, jump (by jump_dest)]
  have rd3811 := evm_run rd3688 with [
    jumpdest, push0, push2 ⟨3699⟩, dup4, dup4, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, push0, push2 ⟨3675⟩, push0, not, dup5, push1 ⟨8⟩, mul,
    push2 ⟨3648⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shr, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, not, dup1, dup4, and, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, swap2, pop, dup3, push1 ⟨2⟩, mul, dup3, or, swap1, pop,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [appendToHistoryShortPackedHeader] using rd3811⟩

theorem stringStoreX_appendToHistoryStoreShortElementHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret header payloadWord aw : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3811⟩
      [header, payloadWord, ⟨0⟩, ⟨32⟩, ⟨0⟩,
        appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      aw
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨3914⟩
        [⟨0⟩, ⟨32⟩, ⟨0⟩,
          appendToHistoryHelperLoadedLen I.calldata len payloadStart,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
          appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        aw
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header) k' C' := by
  have rd3813 := evm_run rd with [jumpdest, dup7]
  obtain ⟨_, _, rd3814⟩ := rd3813.sstore hperm (by native_decide) (by evm_ov)
  have rd3914 := evm_run rd3814 with [pop, push2 ⟨3914⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [appendToHistoryShortElementWriteMap] using rd3914⟩

theorem stringStoreX_appendToHistoryReturnFromShortWriteHelper {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret header aw : UInt256} {k C : Nat}
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3914⟩
      [⟨0⟩, ⟨32⟩, ⟨0⟩,
        appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      aw
      ByteArray.empty
      (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1880⟩
        [appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ret, stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        aw
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header) k' C' := by
  have rd1880 := evm_run rd with [
    jumpdest, pop, pop, pop, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd1880⟩

theorem stringStoreX_appendToHistoryReturnAfterShortWrite {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret header aw : UInt256} {k C : Nat}
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1880⟩
      [appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      aw
      ByteArray.empty
      (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ret
        [appendToHistoryShortReturnLength σ I I.calldata len payloadStart header,
          stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        aw
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header) k' C' := by
  have rd1885 := evm_run rd with [
    jumpdest, pop, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd1886⟩ := rd1885.sload (by native_decide) (by evm_ov)
  have rdret := evm_run rd1886 with [
    swap1, pop, swap2, pop, pop, swap3, swap2, pop, pop,
    raw jump (by native_decide) hret (by evm_ov)]
  exact ⟨_, _, by
    simpa [appendToHistoryShortReturnLength, appendToHistoryFirstStorageSlot] using rdret⟩

theorem stringStoreX_appendToHistoryShortEmptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hzero :
      appendToHistoryHelperLoadedLen I.calldata len payloadStart = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3788⟩
      [⟨0⟩, ⟨32⟩, ⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ret
        [appendToHistoryShortReturnLength σ I I.calldata len payloadStart ⟨0⟩,
          stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart ⟨0⟩) k' C' := by
  obtain ⟨k3811, C3811, rd3811⟩ :=
    stringStoreX_appendToHistoryNewValueShortEmptyPacked (σ := σ) hzero rd
  have rd3811' : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3811⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨32⟩, ⟨0⟩,
        appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k3811 C3811 := by
    simpa [hzero] using rd3811
  obtain ⟨_, _, rd3914⟩ :=
    stringStoreX_appendToHistoryStoreShortElementHeader (σ := σ) (header := ⟨0⟩)
      (payloadWord := ⟨0⟩) hperm rd3811'
  obtain ⟨_, _, rd1880⟩ :=
    stringStoreX_appendToHistoryReturnFromShortWriteHelper (σ := σ) rd3914
  exact stringStoreX_appendToHistoryReturnAfterShortWrite (σ := σ)
    (header := ⟨0⟩) hret rd1880

theorem stringStoreX_appendToHistoryShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hnonzero :
      (appendToHistoryHelperLoadedLen I.calldata len payloadStart).isZero = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3788⟩
      [⟨0⟩, ⟨32⟩, ⟨0⟩, appendToHistoryHelperLoadedLen I.calldata len payloadStart,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperMloadAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ret
        [appendToHistoryShortReturnLength σ I I.calldata len payloadStart
            (appendToHistoryShortPackedHeader
              (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
              (appendToHistoryHelperLoadedLen I.calldata len payloadStart)),
          stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperPayloadAw len)
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart
          (appendToHistoryShortPackedHeader
            (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
            (appendToHistoryHelperLoadedLen I.calldata len payloadStart))) k' C' := by
  obtain ⟨_, _, rd3801⟩ :=
    stringStoreX_appendToHistoryNewValueShortPayloadLoaded (σ := σ) hnonzero rd
  obtain ⟨_, _, rd3811⟩ :=
    stringStoreX_appendToHistoryNewValueShortPayloadPacked (σ := σ) rd3801
  obtain ⟨_, _, rd3914⟩ :=
    stringStoreX_appendToHistoryStoreShortElementHeader (σ := σ)
      (header :=
        appendToHistoryShortPackedHeader
          (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
          (appendToHistoryHelperLoadedLen I.calldata len payloadStart))
      (payloadWord := appendToHistoryHelperPayloadWord I.calldata len payloadStart)
      hperm rd3811
  obtain ⟨_, _, rd1880⟩ :=
    stringStoreX_appendToHistoryReturnFromShortWriteHelper (σ := σ) rd3914
  exact stringStoreX_appendToHistoryReturnAfterShortWrite (σ := σ)
    (header :=
      appendToHistoryShortPackedHeader
        (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
        (appendToHistoryHelperLoadedLen I.calldata len payloadStart))
    hret rd1880

theorem stringStoreX_appendToHistoryHelperShortEmptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hlenOk :
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (hheader :
      appendToHistoryExistingElementHeader σ I I.calldata len payloadStart = ⟨0⟩)
    (hshort :
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart) ⟨31⟩ = ⟨0⟩)
    (hzero :
      appendToHistoryHelperLoadedLen I.calldata len payloadStart = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      [appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperEntryAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ret
        [appendToHistoryShortReturnLength σ I I.calldata len payloadStart ⟨0⟩,
          stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperMloadAw len)
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart ⟨0⟩) k' C' := by
  obtain ⟨_, _, rd3724⟩ :=
    stringStoreX_appendToHistoryReadHelperMemoryLength (σ := σ) rd
  obtain ⟨_, _, rd3749⟩ :=
    stringStoreX_appendToHistoryHelperLengthBoundOk (σ := σ) hlenOk rd3724
  obtain ⟨_, _, rd3189⟩ :=
    stringStoreX_appendToHistoryLoadExistingElementHeader (σ := σ) rd3749
  obtain ⟨_, _, rd3759⟩ :=
    stringStoreX_appendToHistoryDecodeExistingHeaderZero (σ := σ) hheader rd3189
  obtain ⟨_, _, rd3770⟩ :=
    stringStoreX_appendToHistorySkipClearOldZero (σ := σ) rd3759
  obtain ⟨_, _, rd3788⟩ :=
    stringStoreX_appendToHistoryNewValueShortBranch (σ := σ) hshort rd3770
  exact stringStoreX_appendToHistoryShortEmptyReturns (σ := σ)
    hperm hret hzero rd3788

theorem stringStoreX_appendToHistoryHelperShortNonemptyReturns {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart ret : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hret : (D_J stringStoreBytecode 0).contains ret = true)
    (hlenOk :
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (hheader :
      appendToHistoryExistingElementHeader σ I I.calldata len payloadStart = ⟨0⟩)
    (hshort :
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart) ⟨31⟩ = ⟨0⟩)
    (hnonzero :
      (appendToHistoryHelperLoadedLen I.calldata len payloadStart).isZero = ⟨0⟩)
    (rd : RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
      [appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨1880⟩,
        appendToHistoryNewElementSlot σ I I.calldata len payloadStart, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ret, stringStoreSelWord I]
      (appendToHistoryHistorySlotMem I.calldata len payloadStart)
      (appendToHistoryHelperEntryAw len)
      ByteArray.empty (cA, appendToHistoryFirstStorageMap σ I) k C) :
    ∃ k' C',
      RD stringStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ret
        [appendToHistoryShortReturnLength σ I I.calldata len payloadStart
            (appendToHistoryShortPackedHeader
              (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
              (appendToHistoryHelperLoadedLen I.calldata len payloadStart)),
          stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperPayloadAw len)
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart
          (appendToHistoryShortPackedHeader
            (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
            (appendToHistoryHelperLoadedLen I.calldata len payloadStart))) k' C' := by
  obtain ⟨_, _, rd3724⟩ :=
    stringStoreX_appendToHistoryReadHelperMemoryLength (σ := σ) rd
  obtain ⟨_, _, rd3749⟩ :=
    stringStoreX_appendToHistoryHelperLengthBoundOk (σ := σ) hlenOk rd3724
  obtain ⟨_, _, rd3189⟩ :=
    stringStoreX_appendToHistoryLoadExistingElementHeader (σ := σ) rd3749
  obtain ⟨_, _, rd3759⟩ :=
    stringStoreX_appendToHistoryDecodeExistingHeaderZero (σ := σ) hheader rd3189
  obtain ⟨_, _, rd3770⟩ :=
    stringStoreX_appendToHistorySkipClearOldZero (σ := σ) rd3759
  obtain ⟨_, _, rd3788⟩ :=
    stringStoreX_appendToHistoryNewValueShortBranch (σ := σ) hshort rd3770
  exact stringStoreX_appendToHistoryShortNonemptyReturns (σ := σ)
    hperm hret hnonzero rd3788

theorem stringStoreX_appendToHistoryReturnFromWrapperGeneric
    {cA gh bl σ σ₀ A I} {g : Sat256} {σ' : AccountMap}
    {retVal freePtr aw awLoad awStore awFinal : UInt256}
    {mem memret : ByteArray}
    {mloadCost mstoreCost finalMloadCost retCost : Nat}
    (hreach : ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨390⟩
      [retVal, stringStoreSelWord I] mem aw ByteArray.empty (cA, σ') k C)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = [⟨64⟩, retVal, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hfreePtr : (if (⟨64⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) =
      awLoad)
    (hmemret : retVal.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32 = memret)
    (hmstoreCost : ∀ s : State, s.machineState.activeWords = awLoad →
      s.machineState.stack =
        [freePtr + ⟨0⟩, retVal, retVal, freePtr + ⟨0⟩, ⟨2542⟩, freePtr + ⟨32⟩,
          freePtr, retVal, ⟨403⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MSTORE = mstoreCost)
    (hawStore : UInt256.ofNat (MachineState.M awLoad.toNat (freePtr + ⟨0⟩).toNat 32) =
      awStore)
    (hfinalMloadCost : ∀ s : State, s.machineState.activeWords = awStore →
      s.machineState.stack = [⟨64⟩, freePtr + ⟨32⟩, stringStoreSelWord I] →
      memoryExpansionCost s .MLOAD = finalMloadCost)
    (hfinalFreePtr : (if (⟨64⟩ : UInt256).toNat ≥ memret.size
        ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = freePtr)
    (hawFinal : UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) =
      awFinal)
    (hretBytes :
      memret.readWithPadding freePtr.toNat
        (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = UInt256.toByteArray retVal)
    (hretCost : ∀ s : State, s.machineState.activeWords = awFinal →
      s.machineState.stack =
        [freePtr, UInt256.sub (freePtr + ⟨32⟩) freePtr, stringStoreSelWord I] →
      memoryExpansionCost s .RETURN = retCost) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray retVal) := by
  obtain ⟨_, _, rd390⟩ := hreach
  have rd392 := evm_run rd390 with [jumpdest, push1 ⟨64⟩]
  have rd393 := rd392.mload mloadCost freePtr awLoad
    (by native_decide) hmloadCost hfreePtr hawLoad (by simp)
  have rd2523 := evm_run rd393 with [
    push2 ⟨403⟩, swap2, swap1, push2 ⟨2523⟩, jump (by jump_dest)]
  have rd2508 := evm_run rd2523 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨2542⟩,
    push0, dup4, add, dup5, push2 ⟨2508⟩, jump (by jump_dest)]
  have rd2414 := evm_run rd2508 with [
    jumpdest, push2 ⟨2517⟩, dup2, push2 ⟨2414⟩, jump (by jump_dest)]
  have rd2517 := evm_run rd2414 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd2542₀ := evm_run rd2517 with [jumpdest, dup3]
  have rd2543 := rd2542₀.mstore mstoreCost memret awStore
    (by native_decide) hmstoreCost hmemret hawStore (by simp)
  have rd2542 := evm_run rd2543 with [pop, pop, jump (by jump_dest)]
  have rd403 := evm_run rd2542 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd405 := evm_run rd403 with [jumpdest, push1 ⟨64⟩]
  have rd406 := rd405.mload finalMloadCost freePtr awFinal
    (by native_decide) hfinalMloadCost hfinalFreePtr hawFinal (by simp)
  have rd409 := evm_run rd406 with [dup1, swap2, sub, swap1]
  exact rd409.ret retCost (UInt256.toByteArray retVal)
    (by native_decide) hretCost hretBytes (by evm_ov)

theorem currentLengthFreePtr_zero_eq_160 :
    currentLengthFreePtr ⟨0⟩ = ⟨160⟩ := by
  native_decide

theorem appendToHistoryLengthWord_eq_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) =
      calldataWord cd (4 + (calldataWord cd 4).toNat) := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have haddr :
      (((⟨4⟩ : UInt256) + calldataWord cd 4).toNat) =
        4 + (calldataWord cd 4).toNat := by
    rw [uadd_toNat]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    rw [Nat.add_comm]
    exact Nat.mod_eq_of_lt (by
      have hsize : 4 + (calldataWord cd 4).toNat < UInt256.size := by
        have hsmall : 4 + (calldataWord cd 4).toNat ≤ 18446744073709551619 := by
          omega
        exact lt_of_le_of_lt hsmall (by norm_num [UInt256.size])
      simpa [Nat.add_comm] using hsize)
  simp [calldataWord, haddr]

theorem appendToHistoryPayloadStart_toNat
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩).toNat =
      4 + (calldataWord cd 4).toNat + 32 := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord cd 4).toNat < 2 ^ 255 := by
    omega
  have hoffSize : (calldataWord cd 4).toNat < UInt256.size :=
    (calldataWord cd 4).val.isLt
  have hoffOfNat :
      (UInt256.ofNat (calldataWord cd 4).toNat).toNat =
        (calldataWord cd 4).toNat :=
    ulit_toNat' _ hoffSize
  rw [← u256_ofNat_toNat (calldataWord cd 4)]
  simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
    (b := (calldataWord cd 4).toNat)
    (c := 32)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign hoffSmall)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign (by omega : 4 + (calldataWord cd 4).toNat < 2 ^ 255))
    (lt_size_of_lt_sign (by omega :
      4 + (calldataWord cd 4).toNat + 32 < 2 ^ 255)))

theorem appendToHistoryStartPlus31_toNat
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩).toNat =
      4 + (calldataWord cd 4).toNat + 31 := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord cd 4).toNat < 2 ^ 255 := by
    omega
  have hoffSize : (calldataWord cd 4).toNat < UInt256.size :=
    (calldataWord cd 4).val.isLt
  have hoffOfNat :
      (UInt256.ofNat (calldataWord cd 4).toNat).toNat =
        (calldataWord cd 4).toNat :=
    ulit_toNat' _ hoffSize
  rw [← u256_ofNat_toNat (calldataWord cd 4)]
  simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
    (b := (calldataWord cd 4).toNat)
    (c := 31)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign hoffSmall)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign (by omega : 4 + (calldataWord cd 4).toNat < 2 ^ 255))
    (lt_size_of_lt_sign (by omega :
      4 + (calldataWord cd 4).toNat + 31 < 2 ^ 255)))

theorem appendToHistoryStart_slt_one
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hsizeSign : cd.size < 2 ^ 255) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨1⟩ := by
  apply slt_lit_one_low hsizeSign
  rw [appendToHistoryStartPlus31_toNat cd hoffMax]
  omega

theorem appendToHistoryLengthMaxWord_zero
    (cd : ByteArray)
    (hlenZero :
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) = ⟨0⟩) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨0⟩ := by
  rw [hlenZero]
  native_decide

theorem appendToHistoryPayloadWord_zero
    (cd : ByteArray)
    (hsize : cd.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenZero :
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) = ⟨0⟩) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat cd.size) = ⟨0⟩ := by
  have hmul :
      UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩ =
        ⟨0⟩ := by
    rw [hlenZero]
    native_decide
  apply ugt_zero
  rw [hmul]
  rw [currentLength_add_zero_toNat]
  rw [appendToHistoryPayloadStart_toNat cd hoffMax]
  rw [ulit_toNat' cd.size hsize]
  exact hlenWord

set_option maxHeartbeats 1200000 in
theorem stringStoreX_appendToHistoryShortEmptyValidReturns
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hheader :
      appendToHistoryExistingElementHeader σ I I.calldata ⟨0⟩
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)) = ⟨0⟩) :
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, appendToHistoryShortElementWriteMap σ I I.calldata ⟨0⟩
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)) ⟨0⟩)
      (UInt256.toByteArray
        (appendToHistoryShortReturnLength σ I I.calldata ⟨0⟩
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)) ⟨0⟩)) := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hlenZero' : len = ⟨0⟩ := by
    simpa [len] using hlenZero
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    appendToHistoryLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    appendToHistoryPayloadWord_zero I.calldata hsize hoffMax hlenWord hlenZero
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    appendToHistoryStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  obtain ⟨_, _, rd1759⟩ := stringStoreX_appendToHistoryDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  obtain ⟨_, _, rd1780⟩ := stringStoreX_appendToHistoryReachMemoryAlloc
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1759
  obtain ⟨_, _, rd1787⟩ := stringStoreX_appendToHistoryMemoryAlloc
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1780
  obtain ⟨_, _, rd1795⟩ := stringStoreX_appendToHistoryMemoryLength
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1787
  obtain ⟨_, _, rd1804⟩ := stringStoreX_appendToHistoryCalldataCopy
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1795
  obtain ⟨_, _, rd1809⟩ := stringStoreX_appendToHistoryMemoryPadding
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1804
  obtain ⟨_, _, rd1832⟩ := stringStoreX_appendToHistoryMemoryCleanup
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1809
  obtain ⟨_, _, rd1845⟩ := stringStoreX_appendToHistoryFirstStorageWrite
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) hperm rd1832
  obtain ⟨_, _, rd3715⟩ := stringStoreX_appendToHistoryReachStringWriteHelper
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1845
  have hloadedZero :
      appendToHistoryHelperLoadedLen I.calldata len payloadStart = ⟨0⟩ := by
    simpa [len, payloadStart, hlenZero'] using
      appendToHistoryHelperLoadedLen_zero I.calldata payloadStart
  have hheader' :
      appendToHistoryExistingElementHeader σ I I.calldata len payloadStart = ⟨0⟩ := by
    simpa [len, payloadStart, hlenZero'] using hheader
  obtain ⟨_, _, rd390⟩ := stringStoreX_appendToHistoryHelperShortEmptyReturns
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩)
    hperm (by native_decide)
    (by rw [hloadedZero]; decide)
    hheader'
    (by rw [hloadedZero]; decide)
    hloadedZero
    rd3715
  let retVal : UInt256 :=
    appendToHistoryShortReturnLength σ I I.calldata len payloadStart ⟨0⟩
  let mem : ByteArray := appendToHistoryHistorySlotMem I.calldata len payloadStart
  let aw : UInt256 := appendToHistoryHelperMloadAw len
  let freePtr : UInt256 := ⟨160⟩
  let awLoad : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memret : ByteArray := retVal.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32
  let awStore : UInt256 := UInt256.ofNat (MachineState.M awLoad.toNat (freePtr + ⟨0⟩).toNat 32)
  let awFinal : UInt256 := UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32)
  have hfreePtr160 : freePtr = ⟨160⟩ := by
    rfl
  have hfreePtrAdd0 : (freePtr + ⟨0⟩ : UInt256).toNat = freePtr.toNat := by
    simpa using currentLength_add_zero_toNat freePtr
  have hread64 :
      mem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    simpa [mem, freePtr, len, payloadStart, hlenZero', currentLengthFreePtr_zero_eq_160] using
      appendToHistoryHistorySlotMem_zero_read64 I.calldata payloadStart
  have hmemSize64 : 64 < mem.size := by
    simpa [mem, len, payloadStart, hlenZero'] using
      appendToHistoryHistorySlotMem_zero_size_gt64 I.calldata payloadStart
  have hmemSize160 : freePtr.toNat ≤ mem.size := by
    rw [hfreePtr160]
    simpa [mem, len, payloadStart, hlenZero'] using
      appendToHistoryHistorySlotMem_zero_size_ge160 I.calldata payloadStart
  have hfreePtrMload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [mem, aw, freePtr, len, payloadStart, hlenZero', currentLengthFreePtr_zero_eq_160] using
      appendToHistoryHistorySlotMem_zero_mload64 I.calldata payloadStart
  have hmemretRead64 :
      memret.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    exact currentLengthReturnWrite_preserves_read64_zero
      (mem := mem) (len := retVal) (freePtr := freePtr)
      (by rw [hfreePtr160]; decide)
      hmemSize160
      hread64
  have hmemretSize64 : 64 < memret.size := by
    change 64 < (retVal.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32).size
    rw [hfreePtrAdd0]
    rw [show freePtr.toNat = 160 by rw [hfreePtr160]; rfl]
    rw [write32_eq (UInt256.toByteArray retVal) mem 160
      (by rw [toByteArray_size])
      (by simpa [show freePtr.toNat = 160 by rw [hfreePtr160]; rfl] using hmemSize160)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, toByteArray_size]
    omega
  have hfinalFreePtrMload :
      (if (⟨64⟩ : UInt256).toNat ≥ memret.size
          ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact currentLength_mload64_of_read64
      (mem := memret) (aw := awStore) (freePtr := freePtr)
      hmemretSize64
      (by
        dsimp [awStore, awLoad, aw, freePtr]
        rw [hlenZero']
        native_decide)
      hmemretRead64
  have hretBytes :
      memret.readWithPadding freePtr.toNat
          (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat =
        UInt256.toByteArray retVal := by
    exact currentLengthReturnWrite_retBytes
      (mem := mem) (len := retVal) (freePtr := freePtr)
      hmemSize160
      (by rw [hfreePtr160]; decide)
  have hret := stringStoreX_appendToHistoryReturnFromWrapperGeneric
    (σ := σ) (σ' := appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart ⟨0⟩)
    (retVal := retVal) (freePtr := freePtr) (aw := aw)
    (awLoad := awLoad) (awStore := awStore) (awFinal := awFinal)
    (mem := mem) (memret := memret)
    (mloadCost := Cₘ awLoad - Cₘ aw)
    (mstoreCost := Cₘ awStore - Cₘ awLoad)
    (finalMloadCost := Cₘ awFinal - Cₘ awStore)
    (retCost :=
      Cₘ (UInt256.ofNat
        (MachineState.M awFinal.toNat freePtr.toNat
          (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat)) - Cₘ awFinal)
    (hreach := ⟨_, _, by simpa [retVal, mem, aw] using rd390⟩)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad])
    hfreePtrMload
    (by rfl)
    (by rfl)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awStore])
    (by rfl)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awFinal])
    hfinalFreePtrMload
    (by rfl)
    hretBytes
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
  simpa [retVal, mem, aw, freePtr, len, payloadStart, hlenZero'] using hret

set_option maxHeartbeats 1200000 in
theorem stringStoreX_appendToHistoryShortNonemptyReachesReturnWrapper
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hlenOk :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
        ⟨18446744073709551615⟩ = ⟨0⟩)
    (hheader :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      appendToHistoryExistingElementHeader σ I I.calldata len payloadStart = ⟨0⟩)
    (hshort :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      UInt256.gt (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
        ⟨31⟩ = ⟨0⟩)
    (hnonzero :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      (appendToHistoryHelperLoadedLen I.calldata len payloadStart).isZero = ⟨0⟩) :
    let len : UInt256 :=
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
    let payloadStart : UInt256 :=
      (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    let header : UInt256 :=
      appendToHistoryShortPackedHeader
        (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
        (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
    ∃ k C,
      RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨390⟩
        [appendToHistoryShortReturnLength σ I I.calldata len payloadStart header,
          stringStoreSelWord I]
        (appendToHistoryHistorySlotMem I.calldata len payloadStart)
        (appendToHistoryHelperPayloadAw len)
        ByteArray.empty
        (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header) k C := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  obtain ⟨_, _, rd1759⟩ := stringStoreX_appendToHistoryDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  obtain ⟨_, _, rd1780⟩ := stringStoreX_appendToHistoryReachMemoryAlloc
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1759
  obtain ⟨_, _, rd1787⟩ := stringStoreX_appendToHistoryMemoryAlloc
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1780
  obtain ⟨_, _, rd1795⟩ := stringStoreX_appendToHistoryMemoryLength
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1787
  obtain ⟨_, _, rd1804⟩ := stringStoreX_appendToHistoryCalldataCopy
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1795
  obtain ⟨_, _, rd1809⟩ := stringStoreX_appendToHistoryMemoryPadding
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1804
  obtain ⟨_, _, rd1832⟩ := stringStoreX_appendToHistoryMemoryCleanup
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1809
  obtain ⟨_, _, rd1845⟩ := stringStoreX_appendToHistoryFirstStorageWrite
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) hperm rd1832
  obtain ⟨_, _, rd3715⟩ := stringStoreX_appendToHistoryReachStringWriteHelper
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩) rd1845
  exact stringStoreX_appendToHistoryHelperShortNonemptyReturns
    (σ := σ) (len := len) (payloadStart := payloadStart) (ret := ⟨390⟩)
    hperm (by native_decide)
    (by simpa [len, payloadStart] using hlenOk)
    (by simpa [len, payloadStart] using hheader)
    (by simpa [len, payloadStart] using hshort)
    (by simpa [len, payloadStart] using hnonzero)
    rd3715

set_option maxHeartbeats 1200000 in
theorem stringStoreX_appendToHistoryShortNonemptyValidReturns
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hheader :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      appendToHistoryExistingElementHeader σ I I.calldata len payloadStart = ⟨0⟩)
    (hnz :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      len.toNat ≠ 0)
    (hlenShort :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      len.toNat < 32)
    (hpayloadBounds :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      payloadStart.toNat + len.toNat ≤ I.calldata.size) :
    let len : UInt256 :=
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
    let payloadStart : UInt256 :=
      (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    let header : UInt256 :=
      appendToHistoryShortPackedHeader
        (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
        (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
    RDret stringStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header)
      (UInt256.toByteArray
        (appendToHistoryShortReturnLength σ I I.calldata len payloadStart header)) := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  let header : UInt256 :=
    appendToHistoryShortPackedHeader
      (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
      (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
  have hnz' : len.toNat ≠ 0 := by simpa [len] using hnz
  have hshort' : len.toNat < 32 := by simpa [len] using hlenShort
  have hpayloadBounds' : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    simpa [len, payloadStart] using hpayloadBounds
  have hlenNe : len ≠ ⟨0⟩ := by
    intro hzero
    exact hnz' (by rw [hzero]; rfl)
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero hlenNe hshort'
  have hconds := appendToHistoryHelperShortNonemptyConditions_of_abiLen
    I.calldata len payloadStart hnz' hshort' hpayloadBounds'
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    appendToHistoryStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    by
      rw [appendToHistoryLengthWord_eq_abi I.calldata hoffMax]
      apply ugt_zero
      rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
      exact Nat.le_of_not_gt hlenMax
  have hreach := stringStoreX_appendToHistoryShortNonemptyReachesReturnWrapper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hsize hperm hwv hsel hsz36 hhi hoffMax hstart hlenMaxWord
    hpayloadWord
    (by simpa [len, payloadStart] using hconds.1)
    (by simpa [len, payloadStart] using hheader)
    (by simpa [len, payloadStart] using hconds.2.1)
    (by simpa [len, payloadStart] using hconds.2.2)
  let retVal : UInt256 :=
    appendToHistoryShortReturnLength σ I I.calldata len payloadStart header
  let mem : ByteArray := appendToHistoryHistorySlotMem I.calldata len payloadStart
  let aw : UInt256 := appendToHistoryHelperPayloadAw len
  let freePtr : UInt256 := ⟨192⟩
  let awLoad : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memret : ByteArray := retVal.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32
  let awStore : UInt256 := UInt256.ofNat (MachineState.M awLoad.toNat (freePtr + ⟨0⟩).toNat 32)
  let awFinal : UInt256 := UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32)
  have hfreePtr192 : freePtr = ⟨192⟩ := by
    rfl
  have hfreePtrAdd0 : (freePtr + ⟨0⟩ : UInt256).toNat = freePtr.toNat := by
    simpa using currentLength_add_zero_toNat freePtr
  have hread64 :
      mem.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    have hread := appendToHistoryHistorySlotMem_read64 I.calldata len payloadStart hnz'
      hpayloadBounds' (appendToHistoryDataEnd_toNat_of_short hshort')
    rw [hfree] at hread
    simpa [mem, freePtr] using hread
  have hmemSize64 : 64 < mem.size := by
    have hgt := appendToHistoryHistorySlotMem_size_gt128 I.calldata len payloadStart hnz'
      hpayloadBounds' (appendToHistoryDataEnd_toNat_of_short hshort')
    simpa [mem] using (show 64 < (appendToHistoryHistorySlotMem I.calldata len payloadStart).size by
      omega)
  have hmemSizeFreePtr : freePtr.toNat ≤ mem.size := by
    rw [hfreePtr192]
    simpa [mem] using
      appendToHistoryHistorySlotMem_size_ge192 I.calldata len payloadStart hnz'
        hpayloadBounds' (appendToHistoryDataEnd_toNat_of_short hshort')
  have hfreePtrMload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact currentLength_mload64_of_read64
      (mem := mem) (aw := aw) (freePtr := freePtr)
      hmemSize64
      (by
        dsimp [aw]
        exact appendToHistoryHelperPayloadAw_mload64_of_short_nonzero hnz' hshort')
      hread64
  have hmemretRead64 :
      memret.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    exact currentLengthReturnWrite_preserves_read64_zero
      (mem := mem) (len := retVal) (freePtr := freePtr)
      (by rw [hfreePtr192]; decide)
      hmemSizeFreePtr
      hread64
  have hmemretSize64 : 64 < memret.size := by
    change 64 < (retVal.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32).size
    rw [hfreePtrAdd0]
    exact writeWord_size_gt64_of_mem
      (mem := mem) (off := freePtr.toNat) (word := retVal)
      hmemSize64 hmemSizeFreePtr
  have hfinalFreePtrMload :
      (if (⟨64⟩ : UInt256).toNat ≥ memret.size
          ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memret.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    exact currentLength_mload64_of_read64
      (mem := memret) (aw := awStore) (freePtr := freePtr)
      hmemretSize64
      (by
        dsimp [awStore, awLoad, aw, freePtr]
        rw [appendToHistoryHelperPayloadAw_eq_7_of_short_nonzero hnz' hshort']
        decide)
      hmemretRead64
  have hretBytes :
      memret.readWithPadding freePtr.toNat
          (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat =
        UInt256.toByteArray retVal := by
    exact currentLengthReturnWrite_retBytes
      (mem := mem) (len := retVal) (freePtr := freePtr)
      hmemSizeFreePtr
      (by rw [hfreePtr192]; decide)
  have hret := stringStoreX_appendToHistoryReturnFromWrapperGeneric
    (σ := σ)
    (σ' := appendToHistoryShortElementWriteMap σ I I.calldata len payloadStart header)
    (retVal := retVal) (freePtr := freePtr) (aw := aw)
    (awLoad := awLoad) (awStore := awStore) (awFinal := awFinal)
    (mem := mem) (memret := memret)
    (mloadCost := Cₘ awLoad - Cₘ aw)
    (mstoreCost := Cₘ awStore - Cₘ awLoad)
    (finalMloadCost := Cₘ awFinal - Cₘ awStore)
    (retCost :=
      Cₘ (UInt256.ofNat
        (MachineState.M awFinal.toNat freePtr.toNat
          (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat)) - Cₘ awFinal)
    (hreach := by
      simpa [len, payloadStart, header, retVal, mem, aw] using hreach)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLoad])
    hfreePtrMload
    (by rfl)
    (by rfl)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awStore])
    (by rfl)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awFinal])
    hfinalFreePtrMload
    (by rfl)
    hretBytes
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
  simpa [len, payloadStart, header, retVal, mem, aw, freePtr] using hret

theorem decodeCalldata_appendToHistory_none_headShort {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (appendToHistoryTransition.params.map Param.name)
      (transitionSignature appendToHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["suffix"] [.string] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen4 : ¬ I.calldata.toList.length < 4 := by
    omega
  have hnotRead : ¬ 32 ≤ I.calldata.toList.length - 4 := by
    omega
  have hread : ABI.readNat? (I.calldata.toList.drop 4) 0 = none := by
    unfold ABI.readNat? ABI.readWord? ABI.readBytes?
    simp [hnotRead]
  rw [if_neg hlen4]
  have hnotHuge :
      ¬ ([ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  rw [if_neg hnotHuge]
  change (match decodeCalldata.decodeArgs ["suffix"] [.string] (I.calldata.toList.drop 4) ∅ with
    | some (store, _) => some store
    | none => none) = none
  simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
    ABI.isDynamicABIType, hread, bind, Option.bind_none, Option.bind_some, if_true]

theorem decodeCalldata_appendToHistory_none_offsetHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldata (appendToHistoryTransition.params.map Param.name)
      (transitionSignature appendToHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["suffix"] [.string] I.calldata = none
  exact decodeCalldata_string_none_offset_huge (x := "suffix") hsz36 hoff

theorem decodeCalldata_appendToHistory_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (appendToHistoryTransition.params.map Param.name)
      (transitionSignature appendToHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["suffix"] [.string] I.calldata = none
  exact decodeCalldata_string_none_huge (x := "suffix") hbig

theorem decodeCalldata_appendToHistory_none_lengthShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldata (appendToHistoryTransition.params.map Param.name)
      (transitionSignature appendToHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["suffix"] [.string] I.calldata = none
  exact decodeCalldata_string_none_length_short (x := "suffix") hsz36 hhi hshort

theorem decodeCalldata_appendToHistory_some {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    decodeCalldata (appendToHistoryTransition.params.map Param.name)
      (transitionSignature appendToHistoryTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "suffix"
        (.bytes (ByteArray.mk
          ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
            (calldataWord I.calldata
              (4 + (calldataWord I.calldata 4).toNat)).toNat).toArray)))) := by
  show decodeCalldata ["suffix"] [.string] I.calldata =
      some ((∅ : Store).insert "suffix"
        (.bytes (ByteArray.mk
          ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
            (calldataWord I.calldata
              (4 + (calldataWord I.calldata 4).toNat)).toNat).toArray))))
  exact decodeCalldata_string_some (x := "suffix") hsz36 hhi hoffMax hlenWord
    hlenMax hpayload

def appendToHistoryDecodedSuffix (cd : ByteArray) : ByteArray :=
  ByteArray.mk
    ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray)

set_option maxHeartbeats 800000 in
theorem appendToHistoryDecodedSuffix_eq_extract {cd : ByteArray}
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    let len : UInt256 :=
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)
    let payloadStart : UInt256 :=
      (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩)
    appendToHistoryDecodedSuffix cd =
      cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat) := by
  let len : UInt256 :=
    uInt256OfByteArray
      (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩)
  have hlenWord : len = calldataWord cd (4 + (calldataWord cd 4).toNat) := by
    simpa [len] using appendToHistoryLengthWord_eq_abi cd hoffMax
  have hstart : payloadStart.toNat = 4 + (calldataWord cd 4).toNat + 32 := by
    simpa [payloadStart] using appendToHistoryPayloadStart_toNat cd hoffMax
  apply ByteArray.ext
  apply Array.toList_inj.mp
  unfold appendToHistoryDecodedSuffix
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [byteArray_toList_eq]
  rw [List.extract_eq_take_drop]
  rw [hstart]
  rw [show
      4 + (calldataWord cd 4).toNat + 32 +
            (uInt256OfByteArray
              (cd.readBytes ({ val := 4 } + calldataWord cd 4).toNat 32)).toNat -
          (4 + (calldataWord cd 4).toNat + 32) =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat by
      have hlenNat := congrArg UInt256.toNat hlenWord
      dsimp [len] at hlenNat
      rw [← hlenNat]
      omega]
  rw [show
      List.drop ((calldataWord cd 4).toNat + 32) (List.drop 4 cd.data.toList) =
        List.drop (4 + (calldataWord cd 4).toNat + 32) cd.data.toList by
      rw [List.drop_drop]
      congr 1]

theorem appendToHistoryDecodedSuffix_size {cd : ByteArray}
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    (appendToHistoryDecodedSuffix cd).size =
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat := by
  unfold appendToHistoryDecodedSuffix
  show
    (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray.size =
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  simpa using hpayload

theorem appendToHistory_payloadBounds_of_decoded {cd : ByteArray}
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat))
    (hnz :
      let len : UInt256 :=
        uInt256OfByteArray
          (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)
      len.toNat ≠ 0) :
    let len : UInt256 :=
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)
    let payloadStart : UInt256 :=
      (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩)
    payloadStart.toNat + len.toNat ≤ cd.size := by
  let len : UInt256 :=
    uInt256OfByteArray
      (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩)
  have hlenWord : len = calldataWord cd (4 + (calldataWord cd 4).toNat) := by
    simpa [len] using appendToHistoryLengthWord_eq_abi cd hoffMax
  have hstart : payloadStart.toNat = 4 + (calldataWord cd 4).toNat + 32 := by
    simpa [payloadStart] using appendToHistoryPayloadStart_toNat cd hoffMax
  let n : Nat := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  let l : List UInt8 := (cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)
  have hpayload' : (l.take n).length = n := by
    simpa [l, n] using hpayload
  have htakeLen :
      n ≤ l.length := by
    have hle := List.length_take_le' n l
    rw [hpayload'] at hle
    exact hle
  have htakeLen' :
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤
        cd.size - (4 + ((calldataWord cd 4).toNat + 32)) := by
    simpa [n, l, List.drop_drop, byteArray_toList_eq, Array.length_toList] using htakeLen
  have hnz' : (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≠ 0 := by
    simpa [len, hlenWord] using hnz
  have hnpos : 0 < n := by
    simpa [n] using Nat.pos_of_ne_zero hnz'
  have hlpos : 0 < l.length := lt_of_lt_of_le hnpos htakeLen
  have hsubPos : 0 < cd.size - (4 + ((calldataWord cd 4).toNat + 32)) := by
    simpa [l, List.drop_drop, byteArray_toList_eq, Array.length_toList] using hlpos
  have hstartLe : 4 + ((calldataWord cd 4).toNat + 32) ≤ cd.size := by
    omega
  change payloadStart.toNat + len.toNat ≤ cd.size
  rw [hlenWord, hstart]
  omega

theorem decodeCalldata_appendToHistory_none_payloadShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    decodeCalldata (appendToHistoryTransition.params.map Param.name)
      (transitionSignature appendToHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["suffix"] [.string] I.calldata = none
  exact decodeCalldata_string_none_payload_short (x := "suffix") hsz36 hhi hoffMax
    hlenWord hlenMax hpayload

theorem decodeCalldata_appendToHistory_none_lengthHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    decodeCalldata (appendToHistoryTransition.params.map Param.name)
      (transitionSignature appendToHistoryTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["suffix"] [.string] I.calldata = none
  exact decodeCalldata_string_none_length_huge (x := "suffix") hsz36 hhi hoffMax
    hlenWord hlenHuge

theorem stringStoreAppendToHistoryHeadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_appendToHistory_none_headShort (I := I) hsz hshort
  have hrev := stringStoreX_appendToHistoryDecoderHeadShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreAppendToHistoryHeadHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_appendToHistory_none_huge (I := I) hbig
  have hrev := stringStoreX_appendToHistoryDecoderHeadHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hbig
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreAppendToHistoryLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_appendToHistory_none_lengthShort (I := I) hsz36 hhi hshort
  have hrev := stringStoreX_appendToHistoryDecoderLengthShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreAppendToHistoryOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_appendToHistory_none_offsetHuge (I := I) hsz36 hoff
  have hrev := stringStoreX_appendToHistoryDecoderOffsetHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoff
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreAppendToHistoryPayloadShortRuntimeCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_appendToHistory_none_payloadShort (I := I)
    hsz36 hhi hoffMax hlenWord hlenMax hpayloadList
  have hrev := stringStoreX_appendToHistoryDecoderPayloadShortCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    hstart hlenMaxWord hpayloadWord
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreX_appendToHistoryDecoderLengthHugeCore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachAppendToHistoryDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have rd2842 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd2851 := RD.pushConst rd2842 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd2866 := evm_run rd2851 with [
    dup2, gt, iszero, push2 ⟨2866⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd2730 := evm_run rd2866 with [
    jumpdest, push2 ⟨2878⟩, dup6, dup3, dup7, add, push2 ⟨2730⟩,
    jump (by jump_dest)]
  exact stringStoreX_appendStringDecoder2730LengthHuge rd2730
    (by simpa [calldataWord] using hstart)
    (by simpa [calldataWord] using hlenMax)
    (by evm_ov)

theorem appendToHistoryLengthMaxWord_of_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨0⟩ := by
  rw [appendToHistoryLengthWord_eq_abi cd hoffMax]
  apply ugt_zero
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
  exact Nat.le_of_not_gt hlenMax

theorem appendToHistoryLengthMaxWord_one_of_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨1⟩ := by
  rw [appendToHistoryLengthWord_eq_abi cd hoffMax]
  apply ugt_one
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
  exact hlenHuge

theorem stringStoreAppendToHistoryLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_appendToHistory_none_lengthHuge (I := I)
    hsz36 hhi hoffMax hlenWord hlenHuge
  have hrev := stringStoreX_appendToHistoryDecoderLengthHugeCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    (appendToHistoryStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
    (appendToHistoryLengthMaxWord_one_of_abi I.calldata hoffMax hlenHuge)
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreAppendToHistoryPayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact stringStoreAppendToHistoryPayloadShortRuntimeCore
    hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hlenMax
    hpayloadList
    (appendToHistoryStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
    (appendToHistoryLengthMaxWord_of_abi I.calldata hoffMax hlenMax)
    hpayloadWord

theorem appendToHistoryBodyReturns {evm evm' : EVM.State} {suffix : ByteArray} {retLen : Int}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpush :
      pushArray? stringStoreConfig
        { contract := stringStoreContract
          locals := (∅ : Store).insert "suffix" (.bytes suffix) }
        evm historyRef (some (.bytes suffix)) = .ok evm')
    (hlen :
      evalExpr? stringStoreConfig
        { contract := stringStoreContract
          locals := (∅ : Store).insert "suffix" (.bytes suffix) }
        evm' (.arrayLength .storage historyRef) = .ok (.int retLen)) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm
      ((∅ : Store).insert "suffix" (.bytes suffix)) appendToHistoryTransition.body
      (.returned
        { contract := stringStoreContract
          locals := (∅ : Store).insert "suffix" (.bytes suffix) }
        evm' (some (.int retLen))) := by
  let locals : Store := (∅ : Store).insert "suffix" (.bytes suffix)
  let solm : Frame := { contract := stringStoreContract, locals := locals }
  have hsuffix : evalExpr? stringStoreConfig solm evm (.var "suffix") = .ok (.bytes suffix) := by
    simp [solm, locals, evalExpr?, EvalResult.ofOption]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.pushVal hsuffix (by simpa [solm, locals] using hpush)) <|
        ExecBlock.consReturn (ExecStmt.return (by simpa [solm, locals] using hlen))

theorem appendToHistoryBodyReturns_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd suffix : ByteArray) (len payloadStart header : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpush :
      pushArray? stringStoreConfig
        { contract := stringStoreContract
          locals := (∅ : Store).insert "suffix" (.bytes suffix) }
        (initState cA gh bl σ_solm σ₀ g A I) historyRef (some (.bytes suffix)) =
      .ok (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header)) :
    ExecTransitionBody stringStoreConfig stringStoreContract
      (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "suffix" (.bytes suffix))
      appendToHistoryTransition.body
      (.returned
        { contract := stringStoreContract
          locals := (∅ : Store).insert "suffix" (.bytes suffix) }
        (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header)
        (some (.int (Int.ofNat
          (appendToHistoryShortReturnLength σ_evm I cd len payloadStart header).toNat)))) := by
  exact appendToHistoryBodyReturns
    (evm := initState cA gh bl σ_solm σ₀ g A I)
    (evm' := appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g header)
    (suffix := suffix)
    (retLen := Int.ofNat
      (appendToHistoryShortReturnLength σ_evm I cd len payloadStart header).toNat)
    (by simp [initState]; exact hwv)
    hpush
    (appendToHistoryReturnLengthEval_short
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      cd suffix len payloadStart header hAccounts)

theorem appendToHistoryBodyReturns_short_of_existingHeader_zero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd suffix : ByteArray) (len payloadStart : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : suffix.size < 32)
    (hzero :
      appendToHistoryExistingElementHeader σ_evm I cd len payloadStart = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract
      (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "suffix" (.bytes suffix))
      appendToHistoryTransition.body
      (.returned
        { contract := stringStoreContract
          locals := (∅ : Store).insert "suffix" (.bytes suffix) }
        (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I g
          (solidityShortBytesWord suffix))
        (some (.int (Int.ofNat
          (appendToHistoryShortReturnLength σ_evm I cd len payloadStart
            (solidityShortBytesWord suffix)).toNat)))) := by
  exact appendToHistoryBodyReturns_short
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    cd suffix len payloadStart (solidityShortBytesWord suffix) hwv hAccounts
    (appendToHistoryPushArray_short_of_existingHeader_zero
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      cd suffix len payloadStart hAccounts hshort hzero)

theorem appendToHistoryBodyReturns_empty_of_existingHeader_zero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (cd : ByteArray) (len payloadStart : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hzero :
      appendToHistoryExistingElementHeader σ_evm I cd len payloadStart = ⟨0⟩) :
    ExecTransitionBody stringStoreConfig stringStoreContract
      (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "suffix" (.bytes ByteArray.empty))
      appendToHistoryTransition.body
      (.returned
        { contract := stringStoreContract
          locals := (∅ : Store).insert "suffix" (.bytes ByteArray.empty) }
        (appendToHistorySolmEmptyFinalState cA gh bl σ_solm σ₀ A I g)
        (some (.int (Int.ofNat
          (appendToHistoryShortReturnLength σ_evm I cd len payloadStart ⟨0⟩).toNat)))) := by
  exact appendToHistoryBodyReturns
    (evm := initState cA gh bl σ_solm σ₀ g A I)
    (evm' := appendToHistorySolmEmptyFinalState cA gh bl σ_solm σ₀ A I g)
    (suffix := ByteArray.empty)
    (retLen := Int.ofNat
      (appendToHistoryShortReturnLength σ_evm I cd len payloadStart ⟨0⟩).toNat)
    (by simp [initState]; exact hwv)
    (appendToHistoryPushArray_empty_of_existingHeader_zero
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) cd len payloadStart hAccounts hzero)
    (appendToHistoryReturnLengthEval_empty
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) cd len payloadStart hAccounts)

set_option maxHeartbeats 1200000 in
theorem stringStoreAppendToHistoryShortEmptyValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hheader :
      appendToHistoryExistingElementHeader σ_evm I I.calldata ⟨0⟩
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)) = ⟨0⟩) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← appendToHistoryLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
    rw [hlenZeroAbi]
    norm_num [ABI.solcMaxU64]
  have hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) := by
    rw [hlenZeroAbi]
    rfl
  have hdecRaw := decodeCalldata_appendToHistory_some (I := I)
    hsz36 hhi hoffMax hlenWord hlenMax hpayload
  have hdec :
      decodeCalldata (appendToHistoryTransition.params.map Param.name)
        (transitionSignature appendToHistoryTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "suffix" (.bytes ByteArray.empty)) := by
    simpa [hlenZeroAbi] using hdecRaw
  have hret := stringStoreX_appendToHistoryShortEmptyValidReturns
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g)
    hcode hsize hperm hwv hsel hsz36 hhi hoffMax hlenWord hsizeSign hlenZero hheader
  have hbody := appendToHistoryBodyReturns_empty_of_existingHeader_zero
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    I.calldata ⟨0⟩ payloadStart hwv hAccounts (by simpa [payloadStart] using hheader)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by
      simp [appendToHistorySolmEmptyFinalState_createdAccounts])
    (appendToHistoryShortEmptyFinal_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      I.calldata ⟨0⟩ payloadStart hAccounts)
    (returnEquiv_of_encode
      (uint256ReturnEncoding
        (appendToHistoryShortReturnLength σ_evm I I.calldata ⟨0⟩ payloadStart ⟨0⟩)))

set_option maxHeartbeats 1200000 in
theorem stringStoreAppendToHistoryShortNonemptyValidRuntime_of_headerEq
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hheader :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      appendToHistoryExistingElementHeader σ_evm I I.calldata len payloadStart = ⟨0⟩)
    (hnz :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      len.toNat ≠ 0)
    (hlenShort :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      len.toNat < 32)
    (hheaderEq :
      let len : UInt256 :=
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
      let payloadStart : UInt256 :=
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      let suffix : ByteArray := appendToHistoryDecodedSuffix I.calldata
      appendToHistoryShortPackedHeader
          (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
          (appendToHistoryHelperLoadedLen I.calldata len payloadStart) =
        solidityShortBytesWord suffix) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  let suffix : ByteArray := appendToHistoryDecodedSuffix I.calldata
  let header : UInt256 :=
    appendToHistoryShortPackedHeader
      (appendToHistoryHelperPayloadWord I.calldata len payloadStart)
      (appendToHistoryHelperLoadedLen I.calldata len payloadStart)
  have hsel' : ((⟨#[0x7d, 0x4d, 0x56, 0x80]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_appendToHistory (cd := I.calldata) hsel'
  have hdec := decodeCalldata_appendToHistory_some (I := I)
    hsz36 hhi hoffMax hlenWord hlenMax hpayload
  have hdec' :
      decodeCalldata (appendToHistoryTransition.params.map Param.name)
        (transitionSignature appendToHistoryTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "suffix" (.bytes suffix)) := by
    simpa [suffix, appendToHistoryDecodedSuffix] using hdec
  have hbounds := appendToHistory_payloadBounds_of_decoded
    (cd := I.calldata) hoffMax hpayload (by simpa [len] using hnz)
  have hret := stringStoreX_appendToHistoryShortNonemptyValidReturns
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g)
    hcode hsize hperm hwv hsel hsz36 hhi hoffMax hlenWord hsizeSign hlenMax
    hpayloadWord hheader hnz hlenShort hbounds
  have hsuffixSize :
      suffix.size = len.toNat := by
    have hsizeSuffix := appendToHistoryDecodedSuffix_size (cd := I.calldata) hpayload
    have hlenWordEq : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
      simpa [len] using appendToHistoryLengthWord_eq_abi I.calldata hoffMax
    rw [hsizeSuffix, hlenWordEq]
  have hsuffixShort : suffix.size < 32 := by
    rw [hsuffixSize]
    simpa [len] using hlenShort
  have hheaderEq' : header = solidityShortBytesWord suffix := by
    simpa [len, payloadStart, suffix, header] using hheaderEq
  have hbody := appendToHistoryBodyReturns_short_of_existingHeader_zero
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    I.calldata suffix len payloadStart hwv hAccounts hsuffixShort
    (by simpa [len, payloadStart] using hheader)
  have hbody' :
      ExecTransitionBody stringStoreConfig stringStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        ((∅ : Store).insert "suffix" (.bytes suffix))
        appendToHistoryTransition.body
        (.returned
          { contract := stringStoreContract
            locals := (∅ : Store).insert "suffix" (.bytes suffix) }
          (appendToHistorySolmShortFinalState cA gh bl σ_solm σ₀ A I
            (Sat256.ofUInt256 g) header)
          (some (.int (Int.ofNat
            (appendToHistoryShortReturnLength σ_evm I I.calldata len payloadStart header).toNat)))) := by
    simpa [header, hheaderEq'] using hbody
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec' hbody'
    (by
      simp [appendToHistorySolmShortFinalState_createdAccounts])
    (appendToHistoryShortFinal_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      I.calldata len payloadStart header hAccounts)
    (returnEquiv_of_encode
      (uint256ReturnEncoding
        (appendToHistoryShortReturnLength σ_evm I I.calldata len payloadStart header)))

end StringStore
