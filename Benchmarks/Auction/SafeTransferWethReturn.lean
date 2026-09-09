import Benchmarks.Auction.SafeTransferWethRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def auctionSafeTransferDecodedMem (base : UInt256) (mem o : ByteArray) : ByteArray :=
  (UInt256.add base (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
    (UInt256.lnot ⟨31⟩))).toByteArray.write 0 mem 64 32

def auctionSafeTransferDecodedAw (base aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (UInt256.ofNat (MachineState.M
      (UInt256.ofNat (MachineState.M aw.toNat 64 32)).toNat 64 32)).toNat base.toNat 32)

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethReturnLenRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      (⟨1⟩ :: ((⟨68⟩ : UInt256) + base) :: ⟨2835717307⟩ :: weth :: amount :: owner :: ret :: R)
      mem aw o acc k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base)
    (hbad :
      UInt256.slt (UInt256.sub (base + UInt256.ofNat o.size) base) ⟨32⟩ = ⟨1⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add base rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) base aw64 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      hfp (by rfl) (by evm_ov),
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add,
    dup1, push1 ⟨64⟩,
    raw mstore (Cₘ awStore - Cₘ aw64) memRet awStore (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨3568⟩, swap2, swap1, push2 ⟨6062⟩,
    jump (by jump_dest), jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt]
  have rd6069 := rd6062₀
  rw [hbad] at rd6069
  have rd6070₀ := evm_run rd6069 with [iszero]
  have rd6070 := rd6070₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rd6070
  exact evm_run rd6070 with [
    push2 ⟨6078⟩, jumpiNT (by native_decide), push0, dup1,
    raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethReturnShortRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      (⟨1⟩ :: ((⟨68⟩ : UInt256) + base) :: ⟨2835717307⟩ :: weth :: amount :: owner :: ret :: R)
      mem aw o acc k C)
    (hshort : o.size < 32)
    (hbaseAdd : base.toNat + o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbad :
      UInt256.slt (UInt256.sub (base + UInt256.ofNat o.size) base) ⟨32⟩ = ⟨1⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckShort (base := base.toNat) (len := o.size) (words := 1)
        (by simpa using hshort) hbase hbaseAdd
        (by norm_num)
    simpa [hbaseWord, hlenWord] using h
  exact auctionSafeTransferWethReturnLenRevertAt hR rd hfp hbad

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethReturnHugeRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      (⟨1⟩ :: ((⟨68⟩ : UInt256) + base) :: ⟨2835717307⟩ :: weth :: amount :: owner :: ret :: R)
      mem aw o acc k C)
    (hhuge : (2 : Nat) ^ 255 ≤ o.size)
    (hosz : o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbad :
      UInt256.slt (UInt256.sub (base + UInt256.ofNat o.size) base) ⟨32⟩ = ⟨1⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckHuge (base := base.toNat) (len := o.size) (words := 1)
        hhuge hosz hbase (by norm_num)
    simpa [hbaseWord, hlenWord] using h
  exact auctionSafeTransferWethReturnLenRevertAt hR rd hfp hbad

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethReturnBoolToCaller {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth retWord aw : UInt256} {mem o : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      (⟨1⟩ :: ((⟨68⟩ : UInt256) + base) :: ⟨2835717307⟩ :: weth :: amount :: owner :: ret :: R)
      mem aw o acc k C)
    (ho32 : 32 ≤ o.size)
    (hohi : o.size < 2 ^ 255)
    (hbaseAdd : base.toNat + o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base)
    (hword :
      let osz := UInt256.ofNat o.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add base rounded
      let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if base.toNat ≥ memRet.size ∨ base ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding base.toNat 32))) =
      retWord)
    (hcanon : retWord = ⟨0⟩ ∨ retWord = ⟨1⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true) :
    ∃ k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ret R
        (auctionSafeTransferDecodedMem base mem o)
        (auctionSafeTransferDecodedAw base aw) o acc k' C'  := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add base rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoad := UInt256.ofNat (MachineState.M awStore.toNat base.toNat 32)
  have hlenOk :
      UInt256.slt (UInt256.sub (base + osz) base) ⟨32⟩ = ⟨0⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckOk (base := base.toNat) (len := o.size) (words := 1)
        (by simpa using ho32) hohi hbase hbaseAdd
    simpa [osz, hbaseWord, hlenWord] using h
  have hcondCanon :
      UInt256.eq (UInt256.isZero (UInt256.isZero retWord)) retWord = ⟨1⟩ := by
    rcases hcanon with rfl | rfl <;> native_decide
  have hcondCanon' :
      UInt256.eq retWord (UInt256.isZero (UInt256.isZero retWord)) = ⟨1⟩ := by
    rcases hcanon with rfl | rfl <;> native_decide
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) base aw64 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      hfp (by rfl) (by evm_ov),
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add,
    dup1, push1 ⟨64⟩,
    raw mstore (Cₘ awStore - Cₘ aw64) memRet awStore (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨3568⟩, swap2, swap1, push2 ⟨6062⟩,
    jump (by jump_dest), jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt]
  have rd6069 := rd6062₀
  rw [hlenOk] at rd6069
  have rd5350₀ := evm_run rd6069 with [
    iszero, push2 ⟨6078⟩, jumpiT (by native_decide) (by jump_dest), jumpdest, dup2,
    raw mload (Cₘ awLoad - Cₘ awStore) retWord awLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by simpa [osz, rounded, newFree, aw64, memRet, awStore] using hword)
      (by rfl) (by evm_ov),
    dup1, iszero, iszero, dup2, eq]
  have rd5350 := rd5350₀
  rw [hcondCanon'] at rd5350
  have rd3568 := evm_run rd5350 with [
    push2 ⟨5350⟩, jumpiT (by native_decide) (by jump_dest), jumpdest, swap4, swap3,
    pop, pop, pop, jump (by jump_dest), jumpdest, pop]
  exact ⟨_, _, evm_run rd3568 with [jumpdest, pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethReturnNoncanonRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth retWord aw : UInt256} {mem o : ByteArray} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    (hR : R.length ≤ 980)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      (⟨1⟩ :: ((⟨68⟩ : UInt256) + base) :: ⟨2835717307⟩ :: weth :: amount :: owner :: ret :: R)
      mem aw o acc k C)
    (ho32 : 32 ≤ o.size)
    (hohi : o.size < 2 ^ 255)
    (hbaseAdd : base.toNat + o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base)
    (hword :
      let osz := UInt256.ofNat o.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add base rounded
      let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if base.toNat ≥ memRet.size ∨ base ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding base.toNat 32))) =
      retWord)
    (hnz : retWord ≠ ⟨0⟩) (hno : retWord ≠ ⟨1⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add base rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoad := UInt256.ofNat (MachineState.M awStore.toNat base.toNat 32)
  have hlenOk :
      UInt256.slt (UInt256.sub (base + osz) base) ⟨32⟩ = ⟨0⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckOk (base := base.toNat) (len := o.size) (words := 1)
        (by simpa using ho32) hohi hbase hbaseAdd
    simpa [osz, hbaseWord, hlenWord] using h
  have hcondCanon :
      UInt256.eq retWord (UInt256.isZero (UInt256.isZero retWord)) = ⟨0⟩ :=
    auctionTransferReturnBoolNoncanonEqZero hnz hno
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) base aw64 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      hfp (by rfl) (by evm_ov),
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add,
    dup1, push1 ⟨64⟩,
    raw mstore (Cₘ awStore - Cₘ aw64) memRet awStore (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨3568⟩, swap2, swap1, push2 ⟨6062⟩,
    jump (by jump_dest), jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt]
  have rd6069 := rd6062₀
  rw [hlenOk] at rd6069
  have rd5350₀ := evm_run rd6069 with [
    iszero, push2 ⟨6078⟩, jumpiT (by native_decide) (by jump_dest), jumpdest, dup2,
    raw mload (Cₘ awLoad - Cₘ awStore) retWord awLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by simpa [osz, rounded, newFree, aw64, memRet, awStore] using hword)
      (by rfl) (by evm_ov),
    dup1, iszero, iszero, dup2, eq]
  have rd5350 := rd5350₀
  rw [hcondCanon] at rd5350
  exact evm_run rd5350 with [
    push2 ⟨5350⟩, jumpiNT (by native_decide), push0, dup1,
    raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by evm_ov)]

end Auction
