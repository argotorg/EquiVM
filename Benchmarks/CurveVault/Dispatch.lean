import Benchmarks.CurveVault.DispatchPrelude
import Benchmarks.CurveVault.DispatchStele

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault
set_option maxRecDepth 2000
set_option maxHeartbeats 0

/-- `withdraw(uint256,address)`: bucket 3, index 1, body pc 4122. -/
theorem vaultReachWithdraw_uint256_addressBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 0)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨271668728568389⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨16192718⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨16192718⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x00 0xf7 0x14 0xce ⟨16192718⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨16192718⟩ = ⟨271668728568389⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `withdraw(uint256)`: bucket 4, index 4, body pc 4107. -/
theorem vaultReachWithdraw_uint256Body {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 1)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨12976974394821413⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨773487949⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨773487949⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x2e 0x1a 0x7d 0x4d ⟨773487949⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨773487949⟩ = ⟨12976974394821413⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `withdraw(uint256,address,address)`: bucket 4, index 7, body pc 4147. -/
theorem vaultReachWithdraw_uint256_address_addressBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 2)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨50771803027551077⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3026235284⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3026235284⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xb4 0x60 0xaf 0x94 ⟨3026235284⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3026235284⟩ = ⟨50771803027551077⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `totalAssets()`: bucket 0, index 5, body pc 1479. -/
theorem vaultReachTotalAssetsBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 3)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨529763077048069⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨31576340⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨31576340⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x01 0xe1 0xd1 0x14 ⟨31576340⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨31576340⟩ = ⟨529763077048069⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `name()`: bucket 4, index 1, body pc 6437. -/
theorem vaultReachNameBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 4)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨1967979836810501⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨117300739⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨117300739⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x06 0xfd 0xde 0x03 ⟨117300739⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨117300739⟩ = ⟨1967979836810501⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `convertToAssets(uint256)`: bucket 1, index 1, body pc 1859. -/
theorem vaultReachConvertToAssetsBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 5)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨2149344342393637⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨128110906⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨128110906⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x07 0xa2 0xd1 0x3a ⟨128110906⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨128110906⟩ = ⟨2149344342393637⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `approve(address,uint256)`: bucket 4, index 8, body pc 5947. -/
theorem vaultReachApproveBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 6)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨2637349147589445⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨157198259⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨157198259⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 ⟨157198259⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨157198259⟩ = ⟨2637349147589445⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `previewWithdraw(uint256)`: bucket 3, index 2, body pc 4031. -/
theorem vaultReachPreviewWithdrawBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 7)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨2859436604374821⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨170435703⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨170435703⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x0a 0x28 0xa4 0x77 ⟨170435703⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨170435703⟩ = ⟨2859436604374821⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `totalSupply()`: bucket 0, index 10, body pc 6756. -/
theorem vaultReachTotalSupplyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 8)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨6779648240935941⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨404098525⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨404098525⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd ⟨404098525⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨404098525⟩ = ⟨6779648240935941⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `transferFrom(address,address,uint256)`: bucket 4, index 0, body pc 5688. -/
theorem vaultReachTransferFromBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 9)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨10054427659876453⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨599290589⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨599290589⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd ⟨599290589⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨599290589⟩ = ⟨10054427659876453⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `collateral_token()`: bucket 2, index 4, body pc 110. -/
theorem vaultReachCollateral_tokenBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 10)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨10733274385116677⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨639753007⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨639753007⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x26 0x21 0xdb 0x2f ⟨639753007⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨639753007⟩ = ⟨10733274385116677⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `pricePerShare(bool)`: bucket 3, index 7, body pc 1517. -/
theorem vaultReachPricePerShare_boolBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 11)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨11470526258474277⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨683696643⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨683696643⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x28 0xc0 0x62 0x03 ⟨683696643⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨683696643⟩ = ⟨11470526258474277⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `pricePerShare()`: bucket 3, index 0, body pc 1506. -/
theorem vaultReachPricePerShare_Body {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 12)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨43156978247524869⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2572356358⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2572356358⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x99 0x53 0x0b 0x06 ⟨2572356358⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2572356358⟩ = ⟨43156978247524869⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `amm()`: bucket 1, index 3, body pc 122. -/
theorem vaultReachAmmBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 13)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨11984922713553413⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨714357061⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨714357061⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x2a 0x94 0x39 0x45 ⟨714357061⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨714357061⟩ = ⟨11984922713553413⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `decimals()`: bucket 1, index 4, body pc 6426. -/
theorem vaultReachDecimalsBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 14)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨13859229833697797⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨826074471⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨826074471⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x31 0x3c 0xe5 0x67 ⟨826074471⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨826074471⟩ = ⟨13859229833697797⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `asset()`: bucket 0, index 9, body pc 1459. -/
theorem vaultReachAssetBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 15)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨15996992493040389⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨953495055⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨953495055⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x38 0xd5 0x2e 0x0f ⟨953495055⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨953495055⟩ = ⟨15996992493040389⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `increaseAllowance(address,uint256)`: bucket 0, index 7, body pc 6012. -/
theorem vaultReachIncreaseAllowanceBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 16)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨16132667323415621⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨961581905⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨961581905⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x39 0x50 0x93 0x51 ⟨961581905⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨961581905⟩ = ⟨16132667323415621⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `maxDeposit(address)`: bucket 2, index 3, body pc 1936. -/
theorem vaultReachMaxDepositBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 17)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨18064041839136805⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨1076700797⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨1076700797⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x40 0x2d 0x26 0x7d ⟨1076700797⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨1076700797⟩ = ⟨18064041839136805⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `previewRedeem(uint256)`: bucket 3, index 6, body pc 4932. -/
theorem vaultReachPreviewRedeemBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 18)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨21632706694824997⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨1289409798⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨1289409798⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x4c 0xda 0xd5 0x06 ⟨1289409798⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨1289409798⟩ = ⟨21632706694824997⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `deposit(uint256,address)`: bucket 4, index 2, body pc 2143. -/
theorem vaultReachDeposit_uint256_addressBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 19)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨31055978204520261⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨1851080549⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨1851080549⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x6e 0x55 0x3f 0x65 ⟨1851080549⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨1851080549⟩ = ⟨31055978204520261⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `deposit(uint256)`: bucket 0, index 8, body pc 2133. -/
theorem vaultReachDeposit_uint256Body {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 20)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨51427866009163045⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3065339685⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3065339685⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xb6 0xb5 0x5f 0x25 ⟨3065339685⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3065339685⟩ = ⟨51427866009163045⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `balanceOf(address)`: bucket 1, index 0, body pc 6718. -/
theorem vaultReachBalanceOfBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 21)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨31701678421589541⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨1889567281⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨1889567281⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 ⟨1889567281⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨1889567281⟩ = ⟨31701678421589541⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `borrowed_token()`: bucket 3, index 4, body pc 99. -/
theorem vaultReachBorrowed_tokenBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 22)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨33305545993642757⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨1985165238⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨1985165238⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x76 0x53 0x37 0xb6 ⟨1985165238⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨1985165238⟩ = ⟨33305545993642757⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `redeem(uint256,address)`: bucket 2, index 1, body pc 5024. -/
theorem vaultReachRedeem_uint256_addressBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 23)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨34866076123897925⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2078180082⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2078180082⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x7b 0xde 0x82 0xf2 ⟨2078180082⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2078180082⟩ = ⟨34866076123897925⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `redeem(uint256,address,address)`: bucket 4, index 3, body pc 5049. -/
theorem vaultReachRedeem_uint256_address_addressBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 24)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨52363649944369509⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3121116754⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3121116754⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xba 0x08 0x76 0x52 ⟨3121116754⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3121116754⟩ = ⟨52363649944369509⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `redeem(uint256)`: bucket 2, index 9, body pc 5009. -/
theorem vaultReachRedeem_uint256Body {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 25)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨61643477130383653⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3674237557⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3674237557⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xdb 0x00 0x6a 0x75 ⟨3674237557⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3674237557⟩ = ⟨61643477130383653⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `set_max_supply(uint256)`: bucket 0, index 6, body pc 851. -/
theorem vaultReachSet_max_supplyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 26)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨39005789964423973⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2324926255⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2324926255⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x8a 0x93 0x8f 0x2f ⟨2324926255⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2324926255⟩ = ⟨39005789964423973⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `mint(uint256,address)`: bucket 4, index 5, body pc 3146. -/
theorem vaultReachMint_uint256_addressBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 27)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨41868854322547269⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2495578189⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2495578189⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x94 0xbf 0x80 0x4d ⟨2495578189⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2495578189⟩ = ⟨41868854322547269⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `mint(uint256)`: bucket 2, index 2, body pc 3136. -/
theorem vaultReachMint_uint256Body {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 28)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨45160436106805285⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2691771752⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2691771752⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xa0 0x71 0x2d 0x68 ⟨2691771752⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2691771752⟩ = ⟨45160436106805285⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `symbol()`: bucket 0, index 4, body pc 6544. -/
theorem vaultReachSymbolBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 29)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨42177932853612549⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2514000705⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2514000705⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x95 0xd8 0x9b 0x41 ⟨2514000705⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2514000705⟩ = ⟨42177932853612549⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `decreaseAllowance(address,uint256)`: bucket 0, index 2, body pc 6185. -/
theorem vaultReachDecreaseAllowanceBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 30)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨46258390524504389⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2757214935⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2757214935⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xa4 0x57 0xc2 0xd7 ⟨2757214935⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2757214935⟩ = ⟨46258390524504389⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `transfer(address,uint256)`: bucket 2, index 7, body pc 5882. -/
theorem vaultReachTransferBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 31)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨47575441775983173⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2835717307⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2835717307⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xa9 0x05 0x9c 0xbb ⟨2835717307⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2835717307⟩ = ⟨47575441775983173⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `lend_apr()`: bucket 1, index 2, body pc 1107. -/
theorem vaultReachLend_aprBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 32)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨47710324199281413⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨2843756926⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨2843756926⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xa9 0x80 0x49 0x7e ⟨2843756926⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨2843756926⟩ = ⟨47710324199281413⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `previewMint(uint256)`: bucket 0, index 0, body pc 3060. -/
theorem vaultReachPreviewMintBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 33)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨50621475497702437⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3017275065⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3017275065⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xb3 0xd7 0xf6 0xb9 ⟨3017275065⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3017275065⟩ = ⟨50621475497702437⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `borrow_apr()`: bucket 2, index 5, body pc 1020. -/
theorem vaultReachBorrow_aprBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 34)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨52570788968266757⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3133463202⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3133463202⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xba 0xc4 0xda 0xa2 ⟨3133463202⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3133463202⟩ = ⟨52570788968266757⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `factory()`: bucket 2, index 6, body pc 146. -/
theorem vaultReachFactoryBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 35)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨55268057202856453⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3294232917⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3294232917⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xc4 0x5a 0x01 0x55 ⟨3294232917⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3294232917⟩ = ⟨55268057202856453⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `maxMint(address)`: bucket 3, index 9, body pc 2886. -/
theorem vaultReachMaxMintBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 36)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨55799621163370021⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3325916598⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3325916598⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xc6 0x3d 0x75 0xb6 ⟨3325916598⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3325916598⟩ = ⟨55799621163370021⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `convertToShares(uint256)`: bucket 4, index 6, body pc 1782. -/
theorem vaultReachConvertToSharesBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 37)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨55985987780015653⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3337024914⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3337024914⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xc6 0xe6 0xf5 0x92 ⟨3337024914⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3337024914⟩ = ⟨55985987780015653⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `maxWithdraw(address)`: bucket 3, index 5, body pc 3890. -/
theorem vaultReachMaxWithdrawBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 38)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨58149645822407205⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3465988983⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3465988983⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xce 0x96 0xcb 0x77 ⟨3465988983⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3465988983⟩ = ⟨58149645822407205⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `maxSupply()`: bucket 0, index 3, body pc 6414. -/
theorem vaultReachMaxSupplyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 39)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨60143195863453189⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3584813825⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3584813825⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd5 0xab 0xeb 0x01 ⟨3584813825⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3584813825⟩ = ⟨60143195863453189⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `maxRedeem(address)`: bucket 2, index 0, body pc 4783. -/
theorem vaultReachMaxRedeemBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 40)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨61086080720613157⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3641014142⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3641014142⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd9 0x05 0x77 0x7e ⟨3641014142⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3641014142⟩ = ⟨61086080720613157⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `allowance(address,address)`: bucket 3, index 8, body pc 6651. -/
theorem vaultReachAllowanceBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 41)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨62314740941716293⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨3714247998⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨3714247998⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e ⟨3714247998⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨3714247998⟩ = ⟨62314740941716293⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `previewDeposit(uint256)`: bucket 3, index 3, body pc 2056. -/
theorem vaultReachPreviewDepositBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 42)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨67425561853036581⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨4018876663⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨4018876663⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xef 0x8b 0x30 0xf7 ⟨4018876663⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨4018876663⟩ = ⟨67425561853036581⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `controller()`: bucket 2, index 8, body pc 134. -/
theorem vaultReachControllerBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 43)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨69660966064784901⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨4152117137⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨4152117137⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xf7 0x7c 0x47 0x91 ⟨4152117137⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨4152117137⟩ = ⟨69660966064784901⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `admin()`: bucket 2, index 10, body pc 6326. -/
theorem vaultReachAdminBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 44)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨69895560116090373⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨4166100032⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨4166100032⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xf8 0x51 0xa4 0x40 ⟨4166100032⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨4166100032⟩ = ⟨69895560116090373⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

/-- `initialize(address,address,address,address)`: bucket 0, index 1, body pc 158. -/
theorem vaultReachInitializeBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (vaultSelBytes 45)) :
    ∃ k C, RD fork vaultBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 73)
      [⟨70026204933037701⟩, solcSelectorWord I]
      (vaultDispatchMemory ⟨4173887070⟩) (UInt256.ofNat 1) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨4173887070⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xf8 0xc8 0x76 0x5e ⟨4173887070⟩ (by native_decide)
      (by simpa [vaultSelBytes] using hsel)
  have hentry : vaultDispatchEntry ⟨4173887070⟩ = ⟨70026204933037701⟩ := by native_decide
  have hmatch : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ = solcSelectorWord I := by
    rw [hword, hentry]
    native_decide
  obtain ⟨k, C, h⟩ := vaultReachGuard (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hsz hsize hmatch
  exact ⟨k, C, by simpa only [hword, hentry] using h⟩

def vaultSelectorWords : List UInt256 := [⟨16192718⟩, ⟨773487949⟩, ⟨3026235284⟩, ⟨31576340⟩, ⟨117300739⟩, ⟨128110906⟩, ⟨157198259⟩, ⟨170435703⟩, ⟨404098525⟩, ⟨599290589⟩, ⟨639753007⟩, ⟨683696643⟩, ⟨2572356358⟩, ⟨714357061⟩, ⟨826074471⟩, ⟨953495055⟩, ⟨961581905⟩, ⟨1076700797⟩, ⟨1289409798⟩, ⟨1851080549⟩, ⟨3065339685⟩, ⟨1889567281⟩, ⟨1985165238⟩, ⟨2078180082⟩, ⟨3121116754⟩, ⟨3674237557⟩, ⟨2324926255⟩, ⟨2495578189⟩, ⟨2691771752⟩, ⟨2514000705⟩, ⟨2757214935⟩, ⟨2835717307⟩, ⟨2843756926⟩, ⟨3017275065⟩, ⟨3133463202⟩, ⟨3294232917⟩, ⟨3325916598⟩, ⟨3337024914⟩, ⟨3465988983⟩, ⟨3584813825⟩, ⟨3641014142⟩, ⟨3714247998⟩, ⟨4018876663⟩, ⟨4152117137⟩, ⟨4166100032⟩, ⟨4173887070⟩]

/-- Every record read by the two-stage lookup contains one of the 46 ABI selectors. -/
theorem vaultLookupMember (s : UInt256) :
    UInt256.shiftRight (vaultDispatchEntry s) ⟨24⟩ ∈ vaultSelectorWords := by
  have hlt : s.toNat % 5 < 5 := Nat.mod_lt _ (by decide)
  generalize hm : s.toNat % 5 = m at hlt
  interval_cases m
  · have hmod := mod_eq_ofNat (sel := s) (n := 5) (by decide) (by decide) hm
    have hmem : vaultFirstMemory s = vaultFirstMemory (UInt256.ofNat 0) := by
      unfold vaultFirstMemory
      rw [hmod]
      rfl
    have hh : vaultHeader s = UInt256.ofNat 144286232331 := by
      unfold vaultHeader
      rw [hmem]
      native_decide
    have ha : UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 24) = UInt256.ofNat 8600 := by
      rw [hh]; native_decide
    have hb : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 8)) = UInt256.ofNat 8495 := by
      rw [hh]; native_decide
    have hc : UInt256.land (UInt256.ofNat 255) (vaultHeader s) = UInt256.ofNat 11 := by
      rw [hh]; native_decide
    let q := UInt256.shiftRight (UInt256.mul (UInt256.ofNat 8600) s) (UInt256.ofNat 24)
    have hjlt : q.toNat % 11 < 11 := Nat.mod_lt _ (by decide)
    generalize hj : q.toNat % 11 = j at hjlt
    have hjmod := mod_eq_ofNat (sel := q) (n := 11) (by decide) (by decide) hj
    unfold vaultDispatchEntry vaultDispatchMemory
    rw [ha, hb, hc, hmem, show UInt256.mod q (UInt256.ofNat 11) = UInt256.ofNat j from hjmod]
    interval_cases j <;> native_decide
  · have hmod := mod_eq_ofNat (sel := s) (n := 5) (by decide) (by decide) hm
    have hmem : vaultFirstMemory s = vaultFirstMemory (UInt256.ofNat 1) := by
      unfold vaultFirstMemory
      rw [hmod]
      rfl
    have hh : vaultHeader s = UInt256.ofNat 773917701 := by
      unfold vaultHeader
      rw [hmem]
      native_decide
    have ha : UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 24) = UInt256.ofNat 46 := by
      rw [hh]; native_decide
    have hb : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 8)) = UInt256.ofNat 8460 := by
      rw [hh]; native_decide
    have hc : UInt256.land (UInt256.ofNat 255) (vaultHeader s) = UInt256.ofNat 5 := by
      rw [hh]; native_decide
    let q := UInt256.shiftRight (UInt256.mul (UInt256.ofNat 46) s) (UInt256.ofNat 24)
    have hjlt : q.toNat % 5 < 5 := Nat.mod_lt _ (by decide)
    generalize hj : q.toNat % 5 = j at hjlt
    have hjmod := mod_eq_ofNat (sel := q) (n := 5) (by decide) (by decide) hj
    unfold vaultDispatchEntry vaultDispatchMemory
    rw [ha, hb, hc, hmem, show UInt256.mod q (UInt256.ofNat 5) = UInt256.ofNat j from hjmod]
    interval_cases j <;> native_decide
  · have hmod := mod_eq_ofNat (sel := s) (n := 5) (by decide) (by decide) hm
    have hmem : vaultFirstMemory s = vaultFirstMemory (UInt256.ofNat 2) := by
      unfold vaultFirstMemory
      rw [hmod]
      rfl
    have hh : vaultHeader s = UInt256.ofNat 60282683147 := by
      unfold vaultHeader
      rw [hmem]
      native_decide
    have ha : UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 24) = UInt256.ofNat 3593 := by
      rw [hh]; native_decide
    have hb : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 8)) = UInt256.ofNat 8383 := by
      rw [hh]; native_decide
    have hc : UInt256.land (UInt256.ofNat 255) (vaultHeader s) = UInt256.ofNat 11 := by
      rw [hh]; native_decide
    let q := UInt256.shiftRight (UInt256.mul (UInt256.ofNat 3593) s) (UInt256.ofNat 24)
    have hjlt : q.toNat % 11 < 11 := Nat.mod_lt _ (by decide)
    generalize hj : q.toNat % 11 = j at hjlt
    have hjmod := mod_eq_ofNat (sel := q) (n := 11) (by decide) (by decide) hj
    unfold vaultDispatchEntry vaultDispatchMemory
    rw [ha, hb, hc, hmem, show UInt256.mod q (UInt256.ofNat 11) = UInt256.ofNat j from hjmod]
    interval_cases j <;> native_decide
  · have hmod := mod_eq_ofNat (sel := s) (n := 5) (by decide) (by decide) hm
    have hmem : vaultFirstMemory s = vaultFirstMemory (UInt256.ofNat 3) := by
      unfold vaultFirstMemory
      rw [hmod]
      rfl
    have hh : vaultHeader s = UInt256.ofNat 85901474058 := by
      unfold vaultHeader
      rw [hmem]
      native_decide
    have ha : UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 24) = UInt256.ofNat 5120 := by
      rw [hh]; native_decide
    have hb : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 8)) = UInt256.ofNat 8313 := by
      rw [hh]; native_decide
    have hc : UInt256.land (UInt256.ofNat 255) (vaultHeader s) = UInt256.ofNat 10 := by
      rw [hh]; native_decide
    let q := UInt256.shiftRight (UInt256.mul (UInt256.ofNat 5120) s) (UInt256.ofNat 24)
    have hjlt : q.toNat % 10 < 10 := Nat.mod_lt _ (by decide)
    generalize hj : q.toNat % 10 = j at hjlt
    have hjmod := mod_eq_ofNat (sel := q) (n := 10) (by decide) (by decide) hj
    unfold vaultDispatchEntry vaultDispatchMemory
    rw [ha, hb, hc, hmem, show UInt256.mod q (UInt256.ofNat 10) = UInt256.ofNat j from hjmod]
    interval_cases j <;> native_decide
  · have hmod := mod_eq_ofNat (sel := s) (n := 5) (by decide) (by decide) hm
    have hmem : vaultFirstMemory s = vaultFirstMemory (UInt256.ofNat 4) := by
      unfold vaultFirstMemory
      rw [hmod]
      rfl
    have hh : vaultHeader s = UInt256.ofNat 35100130313 := by
      unfold vaultHeader
      rw [hmem]
      native_decide
    have ha : UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 24) = UInt256.ofNat 2092 := by
      rw [hh]; native_decide
    have hb : UInt256.land (UInt256.ofNat 65535) (UInt256.shiftRight (vaultHeader s) (UInt256.ofNat 8)) = UInt256.ofNat 8572 := by
      rw [hh]; native_decide
    have hc : UInt256.land (UInt256.ofNat 255) (vaultHeader s) = UInt256.ofNat 9 := by
      rw [hh]; native_decide
    let q := UInt256.shiftRight (UInt256.mul (UInt256.ofNat 2092) s) (UInt256.ofNat 24)
    have hjlt : q.toNat % 9 < 9 := Nat.mod_lt _ (by decide)
    generalize hj : q.toNat % 9 = j at hjlt
    have hjmod := mod_eq_ofNat (sel := q) (n := 9) (by decide) (by decide) hj
    unfold vaultDispatchEntry vaultDispatchMemory
    rw [ha, hb, hc, hmem, show UInt256.mod q (UInt256.ofNat 9) = UInt256.ofNat j from hjmod]
    interval_cases j <;> native_decide

theorem vaultX_short {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hshort : I.calldata.size < 4) :
    RDrev fork vaultBytecode g (initState σ σ₀ g A I) := by
  apply vaultRevertMismatch hcode
  have hs : UInt256.gt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 3) = ⟨0⟩ := by
    apply ugt_zero
    rw [ulit_toNat' _ (by exact lt_trans hshort (by decide))]
    change I.calldata.size ≤ 3
    omega
  rw [hs, u256_land_zero_left]
  decide

theorem vaultX_noMatch {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vaultBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 46 → (vaultSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev fork vaultBytecode g (initState σ σ₀ g A I) := by
  have hn : UInt256.shiftRight (vaultDispatchEntry (solcSelectorWord I)) ⟨24⟩ ≠ solcSelectorWord I := by
    intro he
    have hm := vaultLookupMember (solcSelectorWord I)
    rw [he] at hm
    simp only [vaultSelectorWords, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45
    · have hz := withdraw_uint256_addressEvmSelector hsz
      have heq : UInt256.eq ⟨16192718⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h0]; native_decide
      rw [hz, hnm 0 (by decide)] at heq
      cases heq
    · have hz := withdraw_uint256EvmSelector hsz
      have heq : UInt256.eq ⟨773487949⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h1]; native_decide
      rw [hz, hnm 1 (by decide)] at heq
      cases heq
    · have hz := withdraw_uint256_address_addressEvmSelector hsz
      have heq : UInt256.eq ⟨3026235284⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h2]; native_decide
      rw [hz, hnm 2 (by decide)] at heq
      cases heq
    · have hz := totalAssetsEvmSelector hsz
      have heq : UInt256.eq ⟨31576340⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h3]; native_decide
      rw [hz, hnm 3 (by decide)] at heq
      cases heq
    · have hz := nameEvmSelector hsz
      have heq : UInt256.eq ⟨117300739⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h4]; native_decide
      rw [hz, hnm 4 (by decide)] at heq
      cases heq
    · have hz := convertToAssetsEvmSelector hsz
      have heq : UInt256.eq ⟨128110906⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h5]; native_decide
      rw [hz, hnm 5 (by decide)] at heq
      cases heq
    · have hz := approveEvmSelector hsz
      have heq : UInt256.eq ⟨157198259⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h6]; native_decide
      rw [hz, hnm 6 (by decide)] at heq
      cases heq
    · have hz := previewWithdrawEvmSelector hsz
      have heq : UInt256.eq ⟨170435703⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h7]; native_decide
      rw [hz, hnm 7 (by decide)] at heq
      cases heq
    · have hz := totalSupplyEvmSelector hsz
      have heq : UInt256.eq ⟨404098525⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h8]; native_decide
      rw [hz, hnm 8 (by decide)] at heq
      cases heq
    · have hz := transferFromEvmSelector hsz
      have heq : UInt256.eq ⟨599290589⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h9]; native_decide
      rw [hz, hnm 9 (by decide)] at heq
      cases heq
    · have hz := collateral_tokenEvmSelector hsz
      have heq : UInt256.eq ⟨639753007⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h10]; native_decide
      rw [hz, hnm 10 (by decide)] at heq
      cases heq
    · have hz := pricePerShare_boolEvmSelector hsz
      have heq : UInt256.eq ⟨683696643⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h11]; native_decide
      rw [hz, hnm 11 (by decide)] at heq
      cases heq
    · have hz := pricePerShare_EvmSelector hsz
      have heq : UInt256.eq ⟨2572356358⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h12]; native_decide
      rw [hz, hnm 12 (by decide)] at heq
      cases heq
    · have hz := ammEvmSelector hsz
      have heq : UInt256.eq ⟨714357061⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h13]; native_decide
      rw [hz, hnm 13 (by decide)] at heq
      cases heq
    · have hz := decimalsEvmSelector hsz
      have heq : UInt256.eq ⟨826074471⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h14]; native_decide
      rw [hz, hnm 14 (by decide)] at heq
      cases heq
    · have hz := assetEvmSelector hsz
      have heq : UInt256.eq ⟨953495055⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h15]; native_decide
      rw [hz, hnm 15 (by decide)] at heq
      cases heq
    · have hz := increaseAllowanceEvmSelector hsz
      have heq : UInt256.eq ⟨961581905⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h16]; native_decide
      rw [hz, hnm 16 (by decide)] at heq
      cases heq
    · have hz := maxDepositEvmSelector hsz
      have heq : UInt256.eq ⟨1076700797⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h17]; native_decide
      rw [hz, hnm 17 (by decide)] at heq
      cases heq
    · have hz := previewRedeemEvmSelector hsz
      have heq : UInt256.eq ⟨1289409798⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h18]; native_decide
      rw [hz, hnm 18 (by decide)] at heq
      cases heq
    · have hz := deposit_uint256_addressEvmSelector hsz
      have heq : UInt256.eq ⟨1851080549⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h19]; native_decide
      rw [hz, hnm 19 (by decide)] at heq
      cases heq
    · have hz := deposit_uint256EvmSelector hsz
      have heq : UInt256.eq ⟨3065339685⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h20]; native_decide
      rw [hz, hnm 20 (by decide)] at heq
      cases heq
    · have hz := balanceOfEvmSelector hsz
      have heq : UInt256.eq ⟨1889567281⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h21]; native_decide
      rw [hz, hnm 21 (by decide)] at heq
      cases heq
    · have hz := borrowed_tokenEvmSelector hsz
      have heq : UInt256.eq ⟨1985165238⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h22]; native_decide
      rw [hz, hnm 22 (by decide)] at heq
      cases heq
    · have hz := redeem_uint256_addressEvmSelector hsz
      have heq : UInt256.eq ⟨2078180082⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h23]; native_decide
      rw [hz, hnm 23 (by decide)] at heq
      cases heq
    · have hz := redeem_uint256_address_addressEvmSelector hsz
      have heq : UInt256.eq ⟨3121116754⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h24]; native_decide
      rw [hz, hnm 24 (by decide)] at heq
      cases heq
    · have hz := redeem_uint256EvmSelector hsz
      have heq : UInt256.eq ⟨3674237557⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h25]; native_decide
      rw [hz, hnm 25 (by decide)] at heq
      cases heq
    · have hz := set_max_supplyEvmSelector hsz
      have heq : UInt256.eq ⟨2324926255⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h26]; native_decide
      rw [hz, hnm 26 (by decide)] at heq
      cases heq
    · have hz := mint_uint256_addressEvmSelector hsz
      have heq : UInt256.eq ⟨2495578189⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h27]; native_decide
      rw [hz, hnm 27 (by decide)] at heq
      cases heq
    · have hz := mint_uint256EvmSelector hsz
      have heq : UInt256.eq ⟨2691771752⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h28]; native_decide
      rw [hz, hnm 28 (by decide)] at heq
      cases heq
    · have hz := symbolEvmSelector hsz
      have heq : UInt256.eq ⟨2514000705⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h29]; native_decide
      rw [hz, hnm 29 (by decide)] at heq
      cases heq
    · have hz := decreaseAllowanceEvmSelector hsz
      have heq : UInt256.eq ⟨2757214935⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h30]; native_decide
      rw [hz, hnm 30 (by decide)] at heq
      cases heq
    · have hz := transferEvmSelector hsz
      have heq : UInt256.eq ⟨2835717307⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h31]; native_decide
      rw [hz, hnm 31 (by decide)] at heq
      cases heq
    · have hz := lend_aprEvmSelector hsz
      have heq : UInt256.eq ⟨2843756926⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h32]; native_decide
      rw [hz, hnm 32 (by decide)] at heq
      cases heq
    · have hz := previewMintEvmSelector hsz
      have heq : UInt256.eq ⟨3017275065⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h33]; native_decide
      rw [hz, hnm 33 (by decide)] at heq
      cases heq
    · have hz := borrow_aprEvmSelector hsz
      have heq : UInt256.eq ⟨3133463202⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h34]; native_decide
      rw [hz, hnm 34 (by decide)] at heq
      cases heq
    · have hz := factoryEvmSelector hsz
      have heq : UInt256.eq ⟨3294232917⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h35]; native_decide
      rw [hz, hnm 35 (by decide)] at heq
      cases heq
    · have hz := maxMintEvmSelector hsz
      have heq : UInt256.eq ⟨3325916598⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h36]; native_decide
      rw [hz, hnm 36 (by decide)] at heq
      cases heq
    · have hz := convertToSharesEvmSelector hsz
      have heq : UInt256.eq ⟨3337024914⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h37]; native_decide
      rw [hz, hnm 37 (by decide)] at heq
      cases heq
    · have hz := maxWithdrawEvmSelector hsz
      have heq : UInt256.eq ⟨3465988983⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h38]; native_decide
      rw [hz, hnm 38 (by decide)] at heq
      cases heq
    · have hz := maxSupplyEvmSelector hsz
      have heq : UInt256.eq ⟨3584813825⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h39]; native_decide
      rw [hz, hnm 39 (by decide)] at heq
      cases heq
    · have hz := maxRedeemEvmSelector hsz
      have heq : UInt256.eq ⟨3641014142⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h40]; native_decide
      rw [hz, hnm 40 (by decide)] at heq
      cases heq
    · have hz := allowanceEvmSelector hsz
      have heq : UInt256.eq ⟨3714247998⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h41]; native_decide
      rw [hz, hnm 41 (by decide)] at heq
      cases heq
    · have hz := previewDepositEvmSelector hsz
      have heq : UInt256.eq ⟨4018876663⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h42]; native_decide
      rw [hz, hnm 42 (by decide)] at heq
      cases heq
    · have hz := controllerEvmSelector hsz
      have heq : UInt256.eq ⟨4152117137⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h43]; native_decide
      rw [hz, hnm 43 (by decide)] at heq
      cases heq
    · have hz := adminEvmSelector hsz
      have heq : UInt256.eq ⟨4166100032⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h44]; native_decide
      rw [hz, hnm 44 (by decide)] at heq
      cases heq
    · have hz := initializeEvmSelector hsz
      have heq : UInt256.eq ⟨4173887070⟩ (solcSelectorWord I) = ⟨1⟩ := by
        rw [h45]; native_decide
      rw [hz, hnm 45 (by decide)] at heq
      cases heq
  apply vaultRevertMismatch hcode
  rw [u256_eq_of_ne hn, u256_land_zero_right]
  decide

end Benchmarks.CurveVault
