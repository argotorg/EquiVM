import Benchmarks.UniswapV4PoolManager.UnlockReturnTrace
import Benchmarks.UniswapV4PoolManager.AllocationPanicGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

/-- A failed allocation of the raw reply has already expanded parent memory beyond the gas bound. -/
theorem unlockRawAllocationGas {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw aw' : UInt256} {σ : AccountMap} {k C C' : Nat} {R : List UInt256}
    (v : PoolManagerImmutables)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hout : out.size < 2^138)
    (hbad : ¬AllocationBounds ⟨160⟩ (UInt256.ofNat out.size))
    (hpaid : Cₘ aw ≤ C)
    (hwords : (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat ≤ aw'.toNat)
    (hcost : C+98+3*((out.size+31)/32)+Cₘ aw' ≤ C'+Cₘ aw)
    (h : RD (deployedRuntime v) I g s0 ⟨7857⟩ R mem aw' out σ k C') :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  have ho : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (lt_trans hout (by decide))
  have he : (allocationEnd ⟨160⟩ (UInt256.ofNat out.size)).toNat = 160+paddedSize out.size := by
    rw [allocationEnd_toNat _ _ (by rw [ho]; change 160+out.size+31 < 2^256; omega), ho]
    rfl
  have hl : 2^64 ≤ 160+paddedSize out.size := by
    by_contra hn
    apply hbad
    constructor
    · rw [he]; change 160 ≤ 160+paddedSize out.size; omega
    · rw [he]; change 160+paddedSize out.size ≤ 2^64-1; omega
  have hpad := paddedSize_le_add31 out.size
  have hpos : (UInt256.ofNat out.size).toNat ≠ 0 := by rw [ho]; omega
  have hw := memoryWords_ge_span aw ⟨160⟩ (UInt256.ofNat out.size) hpos
  rw [ho] at hw
  change (160+out.size+31)/32 ≤ (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat at hw
  have hlarge : (UInt256.ofNat (2^59)).toNat ≤ aw'.toNat := by
    change 2^59 ≤ aw'.toNat
    omega
  have hc := memoryCost_mono hlarge
  have hbound : 324518553658429321982441292826060 < Cₘ (UInt256.ofNat (2^59)) := by decide +kernel
  exact RD.oog_of_cost_gt h (by omega)

/-- Above the critical reply range, the memory and copying costs exceed the gas bound. -/
theorem unlockLargeReplyAllocationGas {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw aw' : UInt256} {σ : AccountMap} {k C C' : Nat} {R : List UInt256}
    (v : PoolManagerImmutables)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hout : out.size < 2^138) (hlarge : 2^63-63 ≤ out.size)
    (hpaid : Cₘ aw+Cₘ (UInt256.ofNat ((out.size+31)/32)) ≤ C)
    (hwords : (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat ≤ aw'.toNat)
    (hcost : C+352+3*((out.size+31)/32)+Cₘ aw' ≤ C'+Cₘ aw)
    (h : RD (deployedRuntime v) I g s0 ⟨7857⟩ R mem aw' out σ k C') :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  have ho : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (lt_trans hout (by decide))
  have hw := memoryWords_ge_span aw ⟨160⟩ (UInt256.ofNat out.size) (by rw [ho]; omega)
  rw [ho] at hw
  change (160+out.size+31)/32 ≤ (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat at hw
  have hp : (UInt256.ofNat (2^58+4)).toNat ≤ aw'.toNat := by
    change 2^58+4 ≤ aw'.toNat
    omega
  have hparent := memoryCost_mono hp
  have hcallee := Cₘ_monotone_of_lt (show 2^58-1 ≤ (out.size+31)/32 by omega)
    (show (out.size+31)/32 < UInt256.size by change _ < 2^256; omega)
  have hbound : 324518553658429321982441292826060 <
      Cₘ (UInt256.ofNat (2^58+4))+Cₘ (UInt256.ofNat (2^58-1))+3*(2^58-1)+352 := by
    decide +kernel
  exact RD.oog_of_cost_gt h (by omega)

/-- In the tight reply range, the callback's 18 operation gas and the panic prefix attain the bound. -/
theorem unlockCriticalReplyAllocationGas {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw aw' : UInt256} {σ : AccountMap} {k C C' : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+2 ≤ 1024)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hout : out.size < 2^138) (hlarge : 2^63-95 ≤ out.size)
    (hpaid : 1094+Cₘ aw+Cₘ (UInt256.ofNat ((out.size+31)/32))+18 ≤ C)
    (hwords : (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat ≤ aw'.toNat)
    (hcost : C+352+3*((out.size+31)/32)+Cₘ aw' ≤ C'+Cₘ aw)
    (h : RD (deployedRuntime v) I g s0 ⟨7857⟩ R mem aw' out σ k C') :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  have ho : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (lt_trans hout (by decide))
  have hw := memoryWords_ge_span aw ⟨160⟩ (UInt256.ofNat out.size) (by rw [ho]; omega)
  rw [ho] at hw
  change (160+out.size+31)/32 ≤ (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat at hw
  have hp : (UInt256.ofNat (2^58+3)).toNat ≤ aw'.toNat := by
    change 2^58+3 ≤ aw'.toNat
    omega
  have hparent := memoryCost_mono hp
  have hcallee := Cₘ_monotone_of_lt (show 2^58-2 ≤ (out.size+31)/32 by omega)
    (show (out.size+31)/32 < UInt256.size by change _ < 2^256; omega)
  have hbound : 324518553658429321982441292826060 =
      Cₘ (UInt256.ofNat (2^58+3))+Cₘ (UInt256.ofNat (2^58-2))+3*(2^58-2)+1487 := by
    decide +kernel
  exact allocationPanicGas v hstack (by omega) h

end Benchmarks.UniswapV4PoolManager
