import Benchmarks.Auction.SettleAuctionTransitions
import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferReturnBoolToEvent {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {amount owner weth retWord aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, ⟨420⟩, ⟨2835717307⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩,
        ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (ho32 : 32 ≤ o.size)
    (hohi : o.size < 2 ^ 255)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩)
    (hword :
      let osz := UInt256.ofNat o.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add ⟨352⟩ rounded
      let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if (⟨352⟩ : UInt256).toNat ≥ memRet.size ∨
          (⟨352⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
      retWord)
    (hcanon : retWord = ⟨0⟩ ∨ retWord = ⟨1⟩) :
    ∃ mem' aw' k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
        [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem' aw' o acc k' C' := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add ⟨352⟩ rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoad := UInt256.ofNat (MachineState.M awStore.toNat (⟨352⟩ : UInt256).toNat 32)
  have hlenOk :
      UInt256.slt (UInt256.sub (UInt256.add ⟨352⟩ osz) ⟨352⟩) ⟨32⟩ = ⟨0⟩ := by
    exact solcReturnStaticLenCheckOk (base := 352) (words := 1)
      (by simpa using ho32) hohi
      (by norm_num [UInt256.size])
      (by
        have hcap : (2 : ℕ) ^ 255 + 352 < UInt256.size := by norm_num [UInt256.size]
        omega)
  have hlenOk' :
      UInt256.slt (UInt256.sub (UInt256.add ⟨352⟩ (UInt256.ofNat o.size)) ⟨352⟩) ⟨32⟩ =
        ⟨0⟩ := by
    simpa [osz] using hlenOk
  have hlenOk'' :
      UInt256.slt (UInt256.sub ((⟨352⟩ : UInt256) + UInt256.ofNat o.size) ⟨352⟩)
          ⟨32⟩ =
        ⟨0⟩ := by
    simpa using hlenOk'
  have hcondCanon :
      UInt256.eq (UInt256.isZero (UInt256.isZero retWord)) retWord = ⟨1⟩ := by
    rcases hcanon with rfl | rfl <;> native_decide
  have hcondCanon' :
      UInt256.eq retWord (UInt256.isZero (UInt256.isZero retWord)) = ⟨1⟩ := by
    rcases hcanon with rfl | rfl <;> native_decide
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) ⟨352⟩ aw64 (by native_decide)
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
  rw [hlenOk''] at rd6069
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
  exact ⟨_, _, _, _, evm_run rd3568 with [jumpdest, pop, pop, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferReturnLenRevert {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, ⟨420⟩, ⟨2835717307⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩,
        ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩)
    (hbad :
      UInt256.slt (UInt256.sub ((⟨352⟩ : UInt256) + UInt256.ofNat o.size) ⟨352⟩)
          ⟨32⟩ =
        ⟨1⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add ⟨352⟩ rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) ⟨352⟩ aw64 (by native_decide)
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

theorem auctionSettleAuctionTransferReturnShortRevert {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, ⟨420⟩, ⟨2835717307⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩,
        ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (hshort : o.size < 32)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbad :
      UInt256.slt (UInt256.sub ((⟨352⟩ : UInt256) + UInt256.ofNat o.size) ⟨352⟩)
          ⟨32⟩ =
        ⟨1⟩ := by
    simpa using
      (solcReturnStaticLenCheckShort (base := 352) (words := 1)
        (len := o.size) (by simpa using hshort)
        (by norm_num [UInt256.size])
        (by
          have hcap : 352 + 32 < UInt256.size := by norm_num [UInt256.size]
          omega)
        (by norm_num))
  exact auctionSettleAuctionTransferReturnLenRevert rd hfp hbad

theorem auctionSettleAuctionTransferReturnHugeRevert {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, ⟨420⟩, ⟨2835717307⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩,
        ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (hhuge : (2 : Nat) ^ 255 ≤ o.size)
    (hosz : o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbad :
      UInt256.slt (UInt256.sub ((⟨352⟩ : UInt256) + UInt256.ofNat o.size) ⟨352⟩)
          ⟨32⟩ =
        ⟨1⟩ := by
    simpa using
      (solcReturnStaticLenCheckHuge (base := 352) (words := 1)
        (len := o.size) hhuge hosz
        (by norm_num [UInt256.size])
        (by norm_num))
  exact auctionSettleAuctionTransferReturnLenRevert rd hfp hbad

theorem auctionTransferReturnBoolNoncanonEqZero {w : UInt256}
    (hnz : w ≠ ⟨0⟩) (hno : w ≠ ⟨1⟩) :
    UInt256.eq w (UInt256.isZero (UInt256.isZero w)) = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro heq
  have hw := uInt256_eq_one_eq heq
  have hzero : UInt256.isZero w = ⟨0⟩ := isZero_eq_zero_of_ne hnz
  have hone : UInt256.isZero (UInt256.isZero w) = ⟨1⟩ := by
    rw [hzero]
    native_decide
  have hwOne : w = ⟨1⟩ := by
    simpa [hone] using hw
  exact hno hwOne

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferReturnNoncanonRevert {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {amount owner weth retWord aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, ⟨420⟩, ⟨2835717307⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩,
        ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (ho32 : 32 ≤ o.size)
    (hohi : o.size < 2 ^ 255)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨352⟩)
    (hword :
      let osz := UInt256.ofNat o.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add ⟨352⟩ rounded
      let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if (⟨352⟩ : UInt256).toNat ≥ memRet.size ∨
          (⟨352⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
      retWord)
    (hnz : retWord ≠ ⟨0⟩) (hno : retWord ≠ ⟨1⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add ⟨352⟩ rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoad := UInt256.ofNat (MachineState.M awStore.toNat (⟨352⟩ : UInt256).toNat 32)
  have hlenOk :
      UInt256.slt (UInt256.sub (UInt256.add ⟨352⟩ osz) ⟨352⟩) ⟨32⟩ = ⟨0⟩ := by
    exact solcReturnStaticLenCheckOk (base := 352) (words := 1)
      (by simpa using ho32) hohi
      (by norm_num [UInt256.size])
      (by
        have hcap : (2 : ℕ) ^ 255 + 352 < UInt256.size := by norm_num [UInt256.size]
        omega)
  have hlenOk'' :
      UInt256.slt (UInt256.sub ((⟨352⟩ : UInt256) + UInt256.ofNat o.size) ⟨352⟩)
          ⟨32⟩ =
        ⟨0⟩ := by
    simpa [osz] using hlenOk
  have hcondCanon :
      UInt256.eq retWord (UInt256.isZero (UInt256.isZero retWord)) = ⟨0⟩ :=
    auctionTransferReturnBoolNoncanonEqZero hnz hno
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) ⟨352⟩ aw64 (by native_decide)
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
  rw [hlenOk''] at rd6069
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

theorem auctionSettleAuctionTransferReturnCopyLen {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
  have houtNat : (UInt256.ofNat out.size).toNat = out.size := by
    simpa using UInt256.toNat_ofNat_of_lt houtSize
  have hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
    change (⟨32⟩ : UInt256).toNat ≤ (UInt256.ofNat out.size).toNat
    rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide, houtNat]
    exact hout32
  simp [min, hle, show (⟨32⟩ : UInt256).toNat = 32 by native_decide]

theorem auctionSettleAuctionTransferReturnCopyLen_le_size {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ out.size := by
  unfold min UInt256.instMin minOfLe
  by_cases hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size
  · simp [hle]
    have hleNat : (⟨32⟩ : UInt256).toNat ≤ (UInt256.ofNat out.size).toNat := hle
    simpa [UInt256.toNat_ofNat_of_lt houtSize] using hleNat
  · simp [hle, UInt256.toNat_ofNat_of_lt houtSize]

theorem auctionSettleAuctionTransferReturnCopyLen_le32 {out : ByteArray} :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ 32 := by
  unfold min UInt256.instMin minOfLe
  by_cases hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size
  · simp [hle]
    decide
  · simp [hle]
    have hnotNat : ¬ 32 ≤ (UInt256.ofNat out.size).toNat := by
      intro hnat
      exact hle hnat
    omega

theorem auctionSettleAuctionTransferReturnMem_size
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (out.write 0
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
      352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).size = 420 := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  have hlen := auctionSettleAuctionTransferReturnCopyLen hout32 houtSize
  have hmem : memTransfer.size = 420 :=
    auctionSettleAuctionWethTransferMem_size noun amount start finish bidder settled owner
  change (out.write 0 memTransfer 352
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).size = 420
  rw [hlen]
  rw [write_eq_gen out memTransfer 352 32 (by decide) hout32 (by rw [hmem]; decide)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem]
  omega

theorem auctionSettleAuctionTransferReturnMem_size_any
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (out.write 0
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
      352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).size = 420 := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hlen32 : len ≤ 32 := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le32 (out := out)
  have hmem : memTransfer.size = 420 :=
    auctionSettleAuctionWethTransferMem_size noun amount start finish bidder settled owner
  change (out.write 0 memTransfer 352 len).size = 420
  by_cases hlen0 : len = 0
  · simpa [hlen0, byteArray_write_len_zero] using hmem
  · rw [write_eq_gen out memTransfer 352 len hlen0 hsrc (by rw [hmem]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem]
    omega

theorem auctionSettleAuctionTransferReturnMem_read64
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (out.write 0
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
      352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 64 32 =
    (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner).readWithPadding
      64 32 := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  have hlen := auctionSettleAuctionTransferReturnCopyLen hout32 houtSize
  have hmem : memTransfer.size = 420 :=
    auctionSettleAuctionWethTransferMem_size noun amount start finish bidder settled owner
  change (out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 64 32 =
    memTransfer.readWithPadding 64 32
  rw [hlen]
  exact write_read_below_gen_extend out memTransfer 352 32 64
    (by decide) hout32 (by rw [hmem]; decide) (by decide)

theorem auctionSettleAuctionTransferReturnMem_read64_any
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (out.write 0
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
      352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 64 32 =
    (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner).readWithPadding
      64 32 := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hmem : memTransfer.size = 420 :=
    auctionSettleAuctionWethTransferMem_size noun amount start finish bidder settled owner
  change (out.write 0 memTransfer 352 len).readWithPadding 64 32 =
    memTransfer.readWithPadding 64 32
  by_cases hlen0 : len = 0
  · simpa [hlen0, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out memTransfer 352 len 64
      hlen0 hsrc (by rw [hmem]; decide) (by decide)

theorem auctionSettleAuctionTransferReturnMem_read352
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (out.write 0
      (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
      352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 352 32 =
    out.extract 0 32 := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  have hlen := auctionSettleAuctionTransferReturnCopyLen hout32 houtSize
  have hmem : memTransfer.size = 420 :=
    auctionSettleAuctionWethTransferMem_size noun amount start finish bidder settled owner
  change (out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 352 32 =
    out.extract 0 32
  rw [hlen]
  exact write32_read_back out memTransfer 352 hout32 (by rw [hmem]; decide)

theorem auctionSettleAuctionTransferReturnMload64
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    let mem :=
      out.write 0
        (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
        352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let aw :=
      UInt256.ofNat
        (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat 352 68) 352 32)
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
    ⟨352⟩ := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  let mem :=
    out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  let aw :=
    UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat 352 68) 352 32)
  have hmemSize : mem.size = 420 := by
    simpa [mem, memTransfer] using
      auctionSettleAuctionTransferReturnMem_size noun amount start finish bidder settled owner
        hout32 houtSize
  have hread : mem.readWithPadding 64 32 = memTransfer.readWithPadding 64 32 := by
    simpa [mem, memTransfer] using
      auctionSettleAuctionTransferReturnMem_read64 noun amount start finish bidder settled owner
        hout32 houtSize
  have hbase :=
    auctionSettleAuctionWethTransferMem_mload64 noun amount start finish bidder settled owner
  have hbaseCond :
      ¬((⟨64⟩ : UInt256).toNat ≥ memTransfer.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩) := by
    rw [auctionSettleAuctionWethTransferMem_size]
    decide
  rw [if_neg hbaseCond] at hbase
  change (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
    ⟨352⟩
  rw [if_neg]
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide, hread] using hbase
  · exact not_or.mpr ⟨by rw [hmemSize]; decide, by native_decide⟩

theorem auctionSettleAuctionTransferReturnMload64_any
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    let mem :=
      out.write 0
        (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
        352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let aw :=
      UInt256.ofNat
        (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat 352 68) 352 32)
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
    ⟨352⟩ := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  let mem :=
    out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  let aw :=
    UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat 352 68) 352 32)
  have hmemSize : mem.size = 420 := by
    simpa [mem, memTransfer] using
      auctionSettleAuctionTransferReturnMem_size_any noun amount start finish bidder settled owner
        houtSize
  have hread : mem.readWithPadding 64 32 = memTransfer.readWithPadding 64 32 := by
    simpa [mem, memTransfer] using
      auctionSettleAuctionTransferReturnMem_read64_any noun amount start finish bidder settled owner
        houtSize
  have hbase :=
    auctionSettleAuctionWethTransferMem_mload64 noun amount start finish bidder settled owner
  have hbaseCond :
      ¬((⟨64⟩ : UInt256).toNat ≥ memTransfer.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩) := by
    rw [auctionSettleAuctionWethTransferMem_size]
    decide
  rw [if_neg hbaseCond] at hbase
  change (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
    ⟨352⟩
  rw [if_neg]
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide, hread] using hbase
  · exact not_or.mpr ⟨by rw [hmemSize]; decide, by native_decide⟩

theorem auctionSettleAuctionTransferReturnMload352
    (noun amount start finish bidder settled owner : UInt256) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    let mem :=
      out.write 0
        (auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner)
        352 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let aw :=
      UInt256.ofNat
        (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat 352 68) 352 32)
    let osz := UInt256.ofNat out.size
    let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
    let newFree := UInt256.add ⟨352⟩ rounded
    let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
    let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
    (if (⟨352⟩ : UInt256).toNat ≥ memRet.size ∨
        (⟨352⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memRet.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  let memTransfer := auctionSettleAuctionWethTransferMem noun amount start finish bidder settled owner
  let mem :=
    out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  let aw :=
    UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat 352 68) 352 32)
  let osz := UInt256.ofNat out.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add ⟨352⟩ rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  have hmemSize : mem.size = 420 := by
    simpa [mem, memTransfer] using
      auctionSettleAuctionTransferReturnMem_size noun amount start finish bidder settled owner
        hout32 houtSize
  have hreadCopy : mem.readWithPadding 352 32 = out.extract 0 32 := by
    simpa [mem, memTransfer] using
      auctionSettleAuctionTransferReturnMem_read352 noun amount start finish bidder settled owner
        hout32 houtSize
  have hmemRetSize : memRet.size = 420 := by
    simpa [memRet] using
      toByteArray_write32_size_of_le mem newFree 64 420 420 hmemSize
        (by rw [hmemSize]; decide) (by decide)
  have hreadRet : memRet.readWithPadding 352 32 = out.extract 0 32 := by
    have hraw :=
      write32_read_above (UInt256.toByteArray newFree) mem 64 352
        (by rw [toByteArray_size]) (by rw [hmemSize]; decide)
        (by decide) (by rw [hmemSize]; decide)
    simpa [memRet, hreadCopy] using hraw
  change (if (⟨352⟩ : UInt256).toNat ≥ memRet.size ∨
        (⟨352⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memRet.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  rw [if_neg]
  · simpa [show (⟨352⟩ : UInt256).toNat = 352 by native_decide, hreadRet]
  · exact not_or.mpr ⟨by rw [hmemRetSize]; decide, by native_decide⟩

theorem evalExpr_safeTransfer_wethNoCode
    (evm : EVM.State) (recipient : AccountAddress) (amount : UInt256) (out : ByteArray)
    (hcode :
      (UInt256.ofNat (((evm.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    evalExpr? auctionConfig
        { contract := auctionContract, locals := auctionSafeTransferFailureStore recipient amount out }
        evm (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) = .ok (.bool false) := by
  have hweth := evalExpr_safeTransfer_weth evm (auctionSafeTransferFailureStore recipient amount out)
    (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef])
  simp [evalExpr?, EvalResult.bind, bind, hweth, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem auctionSafeTransferBodyReverts_lowLevelFailureWethNoCode
    (evm evmCall : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hwethCode :
      (UInt256.ofNat (((evmCall.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount } evm
      safeTransferETHWithFallback.body .reverted := by
  dsimp [safeTransferETHWithFallback, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount)
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_safeTransfer_not_success_true evmCall recipient amount out) (by
      exact ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_safeTransfer_wethNoCode evmCall recipient amount out hwethCode))))

theorem auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethNoCode
    (evm evmBurn evmPay : EVM.State) {out outPay : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_burn out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                  (ret := "_burn") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethNoCode evmBurn evmPay
              (auctionOwnerAddressAt evmBurn) (auctionSettleAuctionAmount evm)
              hpayCall hwethCode))))

theorem auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethNoCode
    (evm evmBurn evmPay : EVM.State) {out outPay : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethNoCode
        (auctionSettleAuctionEnterState evm) evmBurn evmPay
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode))

theorem auctionSafeTransferBodyReverts_lowLevelFailureWethDepositFailure
    (evm evmCall evmDeposit : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmCall.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmCall
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat amount.toNat) []
      (false, evmDeposit, outDeposit) true) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount } evm
      safeTransferETHWithFallback.body .reverted := by
  dsimp [safeTransferETHWithFallback, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount)
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_safeTransfer_not_success_true evmCall recipient amount out) (by
      refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_safeTransfer_wethCode evmCall recipient amount out hwethCode)) ?_
      exact ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (evalExpr_safeTransfer_weth evmCall (auctionSafeTransferFailureStore recipient amount out)
            (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
          (evalExpr_safeTransfer_amount_after_failure evmCall recipient amount out)
          (by rfl) hdeposit)))

theorem auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethDepositFailure
    (evm evmBurn evmPay evmDeposit : EVM.State) {out outPay outDeposit : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (false, evmDeposit, outDeposit) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_burn out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                  (ret := "_burn") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethDepositFailure evmBurn evmPay
              evmDeposit (auctionOwnerAddressAt evmBurn) (auctionSettleAuctionAmount evm)
              hpayCall hwethCode hdeposit))))

theorem auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethDepositFailure
    (evm evmBurn evmPay evmDeposit : EVM.State) {out outPay outDeposit : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (false, evmDeposit, outDeposit) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethDepositFailure
        (auctionSettleAuctionEnterState evm) evmBurn evmPay evmDeposit
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit))

theorem auctionSafeTransferBodyReverts_lowLevelFailureWethTransferFailure
    (evm evmCall evmDeposit evmTransfer : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit outTransfer : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmCall.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmCall
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat amount.toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address recipient, .int (Int.ofNat amount.toNat)]
      (false, evmTransfer, outTransfer) true) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount } evm
      safeTransferETHWithFallback.body .reverted := by
  dsimp [safeTransferETHWithFallback, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount)
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_safeTransfer_not_success_true evmCall recipient amount out) (by
      refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_safeTransfer_wethCode evmCall recipient amount out hwethCode)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (evalExpr_safeTransfer_weth evmCall
            (auctionSafeTransferFailureStore recipient amount out)
            (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
          (evalExpr_safeTransfer_amount_after_failure evmCall recipient amount out)
          (by rfl) hdeposit (auctionExternalABI_decode_deposit outDeposit)) ?_
      exact ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (evalExpr_safeTransfer_weth evmDeposit
            ((auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit)
            (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
          (by simp [evalExpr?, pure])
          (evalExprs_safeTransfer_transfer_args_after_deposit evmDeposit recipient amount out)
          htransfer)))

theorem auctionSafeTransferBodyReverts_lowLevelFailureWethTransferDecodeFailure
    (evm evmCall evmDeposit evmTransfer : EVM.State)
    (recipient : AccountAddress) (amount : UInt256) {out outDeposit outTransfer : ByteArray}
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmCall.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmCall
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmCall evmCall.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat amount.toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address recipient, .int (Int.ofNat amount.toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionSafeTransferStore recipient amount } evm
      safeTransferETHWithFallback.body .reverted := by
  dsimp [safeTransferETHWithFallback, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_safeTransfer_to evm recipient amount)
      (evalExpr_safeTransfer_amount evm recipient amount)
      (evalExpr_safeTransfer_emptyBytes evm recipient amount)
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_safeTransfer_not_success_true evmCall recipient amount out) (by
      refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_safeTransfer_wethCode evmCall recipient amount out hwethCode)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (evalExpr_safeTransfer_weth evmCall
            (auctionSafeTransferFailureStore recipient amount out)
            (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
          (evalExpr_safeTransfer_amount_after_failure evmCall recipient amount out)
          (by rfl) hdeposit (auctionExternalABI_decode_deposit outDeposit)) ?_
      exact ExecBlock.consRevert
        (ExecStmt.externalCallReturnDecodeRevert
          (evalExpr_safeTransfer_weth evmDeposit
            ((auctionSafeTransferFailureStore recipient amount out).insert "_dep" .unit)
            (by simp [auctionSafeTransferFailureStore, auctionSafeTransferStore, wethRef]))
          (by simp [evalExpr?, pure])
          (evalExprs_safeTransfer_transfer_args_after_deposit evmDeposit recipient amount out)
          htransfer htransferDec)))

theorem auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (false, evmTransfer, outTransfer) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_burn out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                  (ret := "_burn") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferFailure
              evmBurn evmPay evmDeposit evmTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer))))

theorem auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (false, evmTransfer, outTransfer) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferFailure
        (auctionSettleAuctionEnterState evm) evmBurn evmPay evmDeposit evmTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer))

theorem auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_settleAuction_bidder_zero_true_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_burn_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_burn out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmBurn
        (ret := "_burn") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmBurn
                  (ret := "_burn") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferDecodeFailure
              evmBurn evmPay evmDeposit evmTransfer (auctionOwnerAddressAt evmBurn)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer
              htransferDec))))

theorem auctionSettleAuctionTransitionReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_burnPayoutLowLevelFailureWethTransferDecodeFailure
        (auctionSettleAuctionEnterState evm) evmBurn evmPay evmDeposit evmTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer htransferDec))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethNoCode
    (evm evmTransfer evmPay : EVM.State) {out outPay : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethNoCode evmTransfer evmPay
              (auctionOwnerAddressAt evmTransfer) (auctionSettleAuctionAmount evm)
              hpayCall hwethCode))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethNoCode
    (evm evmTransfer evmPay : EVM.State) {out outPay : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat = 0) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethNoCode
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethDepositFailure
    (evm evmTransfer evmPay evmDeposit : EVM.State) {out outPay outDeposit : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (false, evmDeposit, outDeposit) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethDepositFailure evmTransfer evmPay
              evmDeposit (auctionOwnerAddressAt evmTransfer) (auctionSettleAuctionAmount evm)
              hpayCall hwethCode hdeposit))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethDepositFailure
    (evm evmTransfer evmPay evmDeposit : EVM.State) {out outPay outDeposit : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (false, evmDeposit, outDeposit) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethDepositFailure
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay evmDeposit
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (false, evmWethTransfer, outTransfer) true) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferFailure
              evmTransfer evmPay evmDeposit evmWethTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (false, evmWethTransfer, outTransfer) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferFailure
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay evmDeposit evmWethTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer))

theorem auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract, locals := auctionSettleAuctionSnapshotStore evm }
          (auctionSettleAuctionMarkSettledState evm)
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig (auctionSettleAuctionMarkSettledState evm)
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount : 0 < (auctionSettleAuctionAmount evm).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount evm).toNat) ByteArray.empty
      (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit" (Int.ofNat (auctionSettleAuctionAmount evm).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount evm).toNat)]
      (true, evmWethTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ } evm
      settleAuctionFn.body .reverted := by
  dsimp [settleAuctionFn, checkedExternalCallStmts]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_settleAuction_snapshot evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_started_true evm hstart)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_not_settled_true evm hsettled)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_time_reached_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (auctionSettleAuctionAssignSettledTrue evm (auctionSettleAuctionSnapshotStore evm)
        (auctionSettleAuctionSnapshotStore_base_auction evm))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_settleAuction_bidder_zero_false_after_markSettled evm hbidder)
      (checkedExternalCallSuccess (cfg := auctionConfig) (C := auctionContract)
        (evm := auctionSettleAuctionMarkSettledState evm)
        (locals := auctionSettleAuctionSnapshotStore evm) hnounsCode
        (evalExpr_settleAuction_nouns_after_markSettled evm)
        (evalExprs_settleAuction_transferFrom_args_after_markSettled evm) hcall
        (auctionExternalABI_decode_transferFrom out))) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (evalExpr_settleAuction_amount_positive_true_after_callResult evm evmTransfer
        (ret := "_tf") .unit (by decide) hamount)
      (by
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (by
              simpa [auctionOwnerAddressAt, auctionSettleAuctionAmount] using
                evalExprs_settleAuction_pay_args_after_callResult evm evmTransfer
                  (ret := "_tf") .unit (by decide) (by decide))
            auctionLookupCallable_safeTransfer
            (bindParams_safeTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm))
            (auctionSafeTransferBodyReverts_lowLevelFailureWethTransferDecodeFailure
              evmTransfer evmPay evmDeposit evmWethTransfer (auctionOwnerAddressAt evmTransfer)
              (auctionSettleAuctionAmount evm) hpayCall hwethCode hdeposit htransfer
              htransferDec))))

theorem auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (true, evmWethTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer = none) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  have henterEnv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
    simpa [auctionSettleAuctionEnterState] using
      storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
  have henterLoad (slot : UInt256) (hne : slot ≠ ⟨101⟩) :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner slot =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
    have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
        evm.executionEnv.codeOwner slot =
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
      simpa [auctionSettleAuctionEnterState] using
        storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
          (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne
    simpa [henterEnv] using hload
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
      (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
      (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReverts_transferFromPayoutLowLevelFailureWethTransferDecodeFailure
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay evmDeposit evmWethTransfer
        (by
          simpa [henterLoad ⟨209⟩ (by decide)] using hstart)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hsettled)
        (by
          have hload210 : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
            Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          simpa [henterEnv, hload210] using htime)
        (by
          simpa [henterLoad ⟨211⟩ (by decide)] using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer htransferDec))

theorem auctionExternalABI_decode_transfer_false {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hsize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) :
    auctionConfig.externalABI.decode? "transfer" out = some [.bool false] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hzero : ABI.bytesToWord ((out.toList.drop 0).take 32) = ⟨0⟩ := by
    simpa [List.drop_zero, hwordList] using hword
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = some (.bool false, 0 + 32) := by
      simpa [decodeScalarWordWithMode?] using
        (decodeScalarWord_bool_ok_zero (bytes := out.toList) (start := 0) htake0 hzero)
    rw [hscalar]
    rfl
  · simpa using hsmall

theorem auctionExternalABI_decode_transfer_true {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hsize : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨1⟩) :
    auctionConfig.externalABI.decode? "transfer" out = some [.bool true] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hone : ABI.bytesToWord ((out.toList.drop 0).take 32) = ⟨1⟩ := by
    simpa [List.drop_zero, hwordList] using hword
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = some (.bool true, 0 + 32) := by
      simpa [decodeScalarWordWithMode?] using
        (decodeScalarWord_bool_ok_one (bytes := out.toList) (start := 0) htake0 hone)
    rw [hscalar]
    rfl
  · simpa using hsmall

theorem auctionExternalABI_decode_transfer_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    auctionConfig.externalABI.decode? "transfer" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = none := by
      rw [← decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.modern)
        (ty := ABIType.elem ElemType.bool) (bytes := out.toList) (start := 0) (by decide)]
      simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
      rw [if_neg htake0]
    rw [hscalar]
    rfl
  · simpa using hsmall

theorem auctionExternalABI_decode_transfer_none_huge {out : ByteArray}
    (hhuge : (2 : Nat) ^ 255 ≤ out.size) :
    auctionConfig.externalABI.decode? "transfer" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhuge⟩)]

theorem auctionExternalABI_decode_transfer_none_noncanon {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hsize : out.size < 2 ^ 255)
    (hnz : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (hno : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨1⟩) :
    auctionConfig.externalABI.decode? "transfer" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsmall : ¬ (2 : Nat) ^ 255 ≤ out.toList.length := by
    rw [hlen]
    omega
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hnzList : ABI.bytesToWord ((out.toList.drop 0).take 32) ≠ ⟨0⟩ := by
    intro h
    exact hnz (by simpa [List.drop_zero, hwordList] using h)
  have hnoList : ABI.bytesToWord ((out.toList.drop 0).take 32) ≠ ⟨1⟩ := by
    intro h
    exact hno (by simpa [List.drop_zero, hwordList] using h)
  simp [auctionConfig, auctionExternalABI, decodeReturn?]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues? boolTy
  rw [if_neg]
  · rw [abiTupleHeadSize_scalarWords_eq (types := [ABIType.elem ElemType.bool]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [ABIType.elem ElemType.bool]) (bytes := out.toList) (cursor := 0)
      (total := 32 * [ABIType.elem ElemType.bool].length)
      (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern (ABIType.elem ElemType.bool)
          out.toList 0 = none := by
      rw [← decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.modern)
        (ty := ABIType.elem ElemType.bool) (bytes := out.toList) (start := 0) (by decide)]
      simp only [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind, Option.bind]
      rw [if_pos htake0]
      have hnzNat : ¬ (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat = 0 := by
        intro h
        exact hnzList (uint256_toNat_eq_zero h)
      have hnoNat : ¬ (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat = 1 := by
        intro h
        apply hnoList
        apply u256_inj
        simpa [UInt256.toNat] using h
      dsimp only [Option.bind]
      rw [if_neg (by simpa [UInt256.toNat] using hnzNat),
        if_neg (by simpa [UInt256.toNat] using hnoNat)]
    rw [hscalar]
    rfl
  · simpa using hsmall

end Auction
