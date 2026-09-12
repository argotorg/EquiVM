import Benchmarks.Dss.Clipper.ListReturnMem

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperListArrayHashMem_keccak_slot (len : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((clipperListArrayHashMem len).readWithPadding (⟨0⟩ : UInt256).toNat
            (⟨32⟩ : UInt256).toNat))) =
      activeDataSlot := by
  simpa [clipperListArrayHashMem, activeDataSlot,
    show (⟨0⟩ : UInt256).toNat = 0 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
    (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) (clipperListArrayLengthMem len)).trans
      (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))

set_option maxHeartbeats 1000000 in
theorem clipperListStorageArrayGetterToBranch {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1812⟩ : UInt256) (ret :: R) solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨1853⟩ : UInt256)
      ((⟨1890⟩ : UInt256) :: UInt256.isZero (solcSlotWord σ ee ⟨11⟩) ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayDataPtr ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayBasePtr ::
        (⟨96⟩ : UInt256) :: ret :: R)
      (clipperListArrayLengthMem (solcSlotWord σ ee ⟨11⟩)) (UInt256.ofNat 5) rdata
      (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd1812, hd1813, hd1815, hd1817, hd1818, hd1819, hd1820, hd1822, hd1823,
      hd1825, hd1826, hd1828, hd1829, hd1830, hd1831, hd1832, hd1834, hd1835,
      hd1836, hd1837, hd1838, hd1839, hd1840, hd1841, hd1842, hd1844, hd1845,
      hd1846, hd1847, hd1848, hd1849, hd1850, _⟩
  let len : UInt256 := solcSlotWord σ ee ⟨11⟩
  have rd1813 := h.jumpdest hd1812 (by evm_ov)
  have rd1815 := rd1813.push1 ⟨96⟩ hd1813 (by evm_ov)
  have rd1817 := rd1815.push1 ⟨11⟩ hd1815 (by evm_ov)
  have rd1818 := rd1817.dup1 hd1817 (by evm_ov)
  obtain ⟨_, _, rd1819raw⟩ := rd1818.sload hd1818 (by evm_ov)
  have rd1819 := by
    simpa [len, solcSlotWord] using rd1819raw
  have rd1820 := rd1819.dup1 hd1819 (by evm_ov)
  have rd1822 := rd1820.push1 ⟨32⟩ hd1820 (by evm_ov)
  have rd1823 := rd1822.mul hd1822 (by evm_ov)
  have rd1825 := rd1823.push1 ⟨32⟩ hd1823 (by evm_ov)
  have rd1826 := rd1825.add hd1825 (by evm_ov)
  have rd1828 := rd1826.push1 ⟨64⟩ hd1826 (by evm_ov)
  have rd1829 := rd1828.mload 0 clipperListArrayBasePtr (UInt256.ofNat 3) hd1828
    mem_cost solcFreePtrMem_mload64 (by native_decide) (by evm_ov)
  have rd1830 := rd1829.swap1 hd1829 (by evm_ov)
  have rd1831 := rd1830.dup2 hd1830 (by evm_ov)
  have rd1832 := rd1831.add hd1831 (by evm_ov)
  have rd1834 := rd1832.push1 ⟨64⟩ hd1832 (by evm_ov)
  have rd1835 := rd1834.mstore 0 (clipperListArrayAllocMem len) (UInt256.ofNat 3)
    hd1834 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1836 := rd1835.dup1 hd1835 (by evm_ov)
  have rd1837 := rd1836.swap3 hd1836 (by evm_ov)
  have rd1838 := rd1837.swap2 hd1837 (by evm_ov)
  have rd1839 := rd1838.swap1 hd1838 (by evm_ov)
  have rd1840 := rd1839.dup2 hd1839 (by evm_ov)
  have rd1841 := rd1840.dup2 hd1840 (by evm_ov)
  have rd1842 := rd1841.mstore 6 (clipperListArrayLengthMem len) (UInt256.ofNat 5)
    hd1841 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1844 := rd1842.push1 ⟨32⟩ hd1842 (by evm_ov)
  have rd1845 := rd1844.add hd1844 (by evm_ov)
  have rd1846 := rd1845.dup3 hd1845 (by evm_ov)
  have rd1847 := rd1846.dup1 hd1846 (by evm_ov)
  obtain ⟨_, _, rd1848raw⟩ := rd1847.sload hd1847 (by evm_ov)
  have rd1848 := by
    simpa [len, solcSlotWord, clipperListArrayDataPtr] using rd1848raw
  have rd1849 := rd1848.dup1 hd1848 (by evm_ov)
  have rd1850 := rd1849.iszero hd1849 (by evm_ov)
  have rd1853 := rd1850.push2 ⟨1890⟩ hd1850 (by evm_ov)
  exact ⟨_, _, by simpa [len, clipperListArrayDataPtr] using rd1853⟩

theorem clipperListStorageArrayGetterEmpty {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1853⟩ : UInt256)
      ((⟨1890⟩ : UInt256) :: UInt256.isZero (solcSlotWord σ ee ⟨11⟩) ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayDataPtr ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayBasePtr ::
        (⟨96⟩ : UInt256) :: ret :: R)
      (clipperListArrayLengthMem (solcSlotWord σ ee ⟨11⟩)) (UInt256.ofNat 5) rdata
      (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (h1890 : (D_J code 0).contains (⟨1890⟩ : UInt256) = true)
    (hret : (D_J code 0).contains ret = true)
    (hlen : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (clipperListArrayBasePtr :: R)
      (clipperListArrayLengthMem (solcSlotWord σ ee ⟨11⟩)) (UInt256.ofNat 5) rdata
      (cA, σ) k' C' := by
  have hwfAll := hwf
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, hd1853, _⟩
  have hcond : UInt256.isZero (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [hlen]
    native_decide
  have rd1890 := h.jumpiT hd1853 hcond h1890 (by evm_ov)
  exact clipperListStorageArrayCleanup rd1890 hwfAll hret (by omega)

theorem clipperListStorageArrayGetter_empty {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1812⟩ : UInt256) (ret :: R) solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (h1890 : (D_J code 0).contains (⟨1890⟩ : UInt256) = true)
    (hret : (D_J code 0).contains ret = true)
    (hlen : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (clipperListArrayBasePtr :: R)
      (clipperListArrayLengthMem (solcSlotWord σ ee ⟨11⟩)) (UInt256.ofNat 5) rdata
      (cA, σ) k' C' := by
  obtain ⟨_, _, rd1853⟩ := clipperListStorageArrayGetterToBranch h hwf hov
  exact clipperListStorageArrayGetterEmpty rd1853 hwf h1890 hret hlen hov

theorem clipperListStorageArrayGetterNonemptyToLoop {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1853⟩ : UInt256)
      ((⟨1890⟩ : UInt256) :: UInt256.isZero (solcSlotWord σ ee ⟨11⟩) ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayDataPtr ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayBasePtr ::
        (⟨96⟩ : UInt256) :: ret :: R)
      (clipperListArrayLengthMem (solcSlotWord σ ee ⟨11⟩)) (UInt256.ofNat 5) rdata
      (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨1870⟩ : UInt256)
      (clipperListArrayDataPtr :: activeDataSlot ::
        clipperListArrayEndPtr (solcSlotWord σ ee ⟨11⟩) ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayBasePtr ::
        (⟨96⟩ : UInt256) :: ret :: R)
      (clipperListArrayHashMem (solcSlotWord σ ee ⟨11⟩)) (UInt256.ofNat 5) rdata
      (cA, σ) k' C' := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, hd1853, hd1854, hd1856, hd1857, hd1858, hd1859, hd1860, hd1861,
      hd1863, hd1864, hd1866, hd1868, hd1869, _⟩
  let len : UInt256 := solcSlotWord σ ee ⟨11⟩
  have hcond : UInt256.isZero (solcSlotWord σ ee ⟨11⟩) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlen
  have rd1854 := h.jumpiNT hd1853 hcond (by evm_ov)
  have rd1856 := rd1854.push1 ⟨32⟩ hd1854 (by evm_ov)
  have rd1857 := rd1856.mul hd1856 (by evm_ov)
  have rd1858 := rd1857.dup3 hd1857 (by evm_ov)
  have rd1859 := rd1858.add hd1858 (by evm_ov)
  have rd1860 := rd1859.swap2 hd1859 (by evm_ov)
  have rd1861 := rd1860.swap1 hd1860 (by evm_ov)
  have rd1863 := rd1861.push1 ⟨0⟩ hd1861 (by evm_ov)
  have rd1864 := rd1863.mstore 0 (clipperListArrayHashMem len) (UInt256.ofNat 5)
    hd1863 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1866 := rd1864.push1 ⟨32⟩ hd1864 (by evm_ov)
  have rd1868 := rd1866.push1 ⟨0⟩ hd1866 (by evm_ov)
  have rd1869 := rd1868.keccak256 0 activeDataSlot (UInt256.ofNat 5)
    hd1868 mem_cost (clipperListArrayHashMem_keccak_slot len) (by native_decide)
    (by evm_ov)
  have rd1870 := rd1869.swap1 hd1869 (by evm_ov)
  exact ⟨_, _, by simpa [len, clipperListArrayEndPtr] using rd1870⟩

theorem clipperListStorageArrayGetter_nonempty_to_loop {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1812⟩ : UInt256) (ret :: R) solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨1870⟩ : UInt256)
      (clipperListArrayDataPtr :: activeDataSlot ::
        clipperListArrayEndPtr (solcSlotWord σ ee ⟨11⟩) ::
        solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayBasePtr ::
        (⟨96⟩ : UInt256) :: ret :: R)
      (clipperListArrayHashMem (solcSlotWord σ ee ⟨11⟩)) (UInt256.ofNat 5) rdata
      (cA, σ) k' C' := by
  obtain ⟨_, _, rd1853⟩ := clipperListStorageArrayGetterToBranch h hwf hov
  exact clipperListStorageArrayGetterNonemptyToLoop rd1853 hwf hlen hov

set_option maxHeartbeats 1000000 in
theorem clipperListStorageArrayLoopStepToBranch {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {dest slot endp : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1870⟩ : UInt256) (dest :: slot :: endp :: R)
      mem aw rdata (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨1889⟩ : UInt256)
      ((⟨1870⟩ : UInt256) :: UInt256.gt endp ((⟨32⟩ : UInt256) + dest) ::
        ((⟨32⟩ : UInt256) + dest) :: ((⟨1⟩ : UInt256) + slot) :: endp :: R)
      (clipperListArrayCopyStepMem σ ee slot dest mem) (clipperListArrayCopyStepAw aw dest)
      rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd1870, hd1871, hd1872, hd1873,
      hd1874, hd1875, hd1877, hd1878, hd1879, hd1881, hd1882, hd1883, hd1884,
      hd1885, hd1886, _⟩
  have rd1871 := h.jumpdest hd1870 (by evm_ov)
  have rd1872 := rd1871.dup2 hd1871 (by evm_ov)
  obtain ⟨_, _, rd1873raw⟩ := rd1872.sload hd1872 (by evm_ov)
  have rd1873 := by
    simpa [solcSlotWord] using rd1873raw
  have rd1874 := rd1873.dup2 hd1873 (by evm_ov)
  have rd1875 := rd1874.mstore (Cₘ (clipperListArrayCopyStepAw aw dest) - Cₘ aw)
    (clipperListArrayCopyStepMem σ ee slot dest mem) (clipperListArrayCopyStepAw aw dest)
    hd1874
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := aw) (off := dest) (val := solcSlotWord σ ee slot)
        (t := dest :: slot :: endp :: R) haw hstk (by rfl))
    (by rfl) (by rfl) (by evm_ov)
  have rd1877 := rd1875.push1 ⟨32⟩ hd1875 (by evm_ov)
  have rd1878 := rd1877.add hd1877 (by evm_ov)
  have rd1879 := rd1878.swap1 hd1878 (by evm_ov)
  have rd1881 := rd1879.push1 ⟨1⟩ hd1879 (by evm_ov)
  have rd1882 := rd1881.add hd1881 (by evm_ov)
  have rd1883 := rd1882.swap1 hd1882 (by evm_ov)
  have rd1884 := rd1883.dup1 hd1883 (by evm_ov)
  have rd1885 := rd1884.dup4 hd1884 (by evm_ov)
  have rd1886 := rd1885.gt hd1885 (by evm_ov)
  have rd1889 := rd1886.push2 ⟨1870⟩ hd1886 (by evm_ov)
  exact ⟨_, _, by simpa [clipperListArrayCopyStepMem, clipperListArrayCopyStepAw] using rd1889⟩

theorem clipperListStorageArrayLoopStepBack {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {dest slot endp : UInt256}
    {a b base ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1870⟩ : UInt256)
      (dest :: slot :: endp :: a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (h1870 : (D_J code 0).contains (⟨1870⟩ : UInt256) = true)
    (hcond : UInt256.gt endp ((⟨32⟩ : UInt256) + dest) ≠ ⟨0⟩)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨1870⟩ : UInt256)
      (((⟨32⟩ : UInt256) + dest) :: ((⟨1⟩ : UInt256) + slot) :: endp ::
        a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      (clipperListArrayCopyStepMem σ ee slot dest mem) (clipperListArrayCopyStepAw aw dest)
      rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd1889⟩ :=
    clipperListStorageArrayLoopStepToBranch (R := a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      h hwf (by simp only [List.length_cons]; omega)
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd1889,
      _⟩
  exact ⟨_, _, rd1889.jumpiT hd1889 hcond h1870 (by evm_ov)⟩

theorem clipperListStorageArrayLoopStepExit {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {dest slot endp : UInt256}
    {a b base ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨1870⟩ : UInt256)
      (dest :: slot :: endp :: a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (hret : (D_J code 0).contains ret = true)
    (hcond : UInt256.gt endp ((⟨32⟩ : UInt256) + dest) = ⟨0⟩)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (base :: R)
      (clipperListArrayCopyStepMem σ ee slot dest mem) (clipperListArrayCopyStepAw aw dest)
      rdata (cA, σ) k' C' := by
  have hwfAll := hwf
  obtain ⟨_, _, rd1889⟩ :=
    clipperListStorageArrayLoopStepToBranch (R := a :: b :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      h hwf (by simp only [List.length_cons]; omega)
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd1889,
      _⟩
  have rd1890 := rd1889.jumpiNT hd1889 hcond (by evm_ov)
  exact clipperListStorageArrayCleanup rd1890 hwfAll hret (by omega)

set_option maxHeartbeats 1000000 in
theorem clipperListStorageArrayLoopFrom {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hwfStorage : clipperStorageWF σ ee)
    (hwf : clipperListStorageArrayGetterWf code)
    (h1870 : (D_J code 0).contains (⟨1870⟩ : UInt256) = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∀ m k,
      (solcSlotWord σ ee ⟨11⟩).toNat = k + m + 1 →
      (∀ k₀ C₀,
        RD code ee g s0 (⟨1870⟩ : UInt256)
          (clipperListArrayDest k :: clipperListArraySlot k ::
            clipperListArrayEndPtr (solcSlotWord σ ee ⟨11⟩) ::
            solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayBasePtr ::
            (⟨96⟩ : UInt256) :: ret :: R)
          (clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩) k)
          (clipperListArrayCopiedAw k) rdata (cA, σ) k₀ C₀ →
        ∃ k' C', RD code ee g s0 ret (clipperListArrayBasePtr :: R)
          (clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩)
            (solcSlotWord σ ee ⟨11⟩).toNat)
          (clipperListArrayCopiedAw (solcSlotWord σ ee ⟨11⟩).toNat)
          rdata (cA, σ) k' C') := by
  intro m
  induction m with
  | zero =>
      intro k hn k₀ C₀ hrd
      have hn' : (solcSlotWord σ ee ⟨11⟩).toNat = k + 1 := by omega
      have hboundSucc : 160 + 32 * (k + 1) < UInt256.size := by
        have hfree := clipperStorageWF_freePtr_lt hwfStorage
        omega
      have hboundK : 160 + 32 * k < UInt256.size := by omega
      have hdestStep := clipperListArrayDest_succ (n := k) hboundSucc
      have hend := clipperListArrayEndPtr_eq_dest_of_wf hwfStorage
      have hcond :
          UInt256.gt (clipperListArrayEndPtr (solcSlotWord σ ee ⟨11⟩))
            ((⟨32⟩ : UInt256) + clipperListArrayDest k) = ⟨0⟩ := by
        rw [hdestStep, hend, hn']
        exact ugt_zero le_rfl
      obtain ⟨_, _, rdret⟩ :=
        clipperListStorageArrayLoopStepExit
          (R := R) (a := solcSlotWord σ ee ⟨11⟩) (b := (⟨11⟩ : UInt256))
          (base := clipperListArrayBasePtr) (ret := ret)
          hrd hwf hret hcond hov
      have hmem :
          clipperListArrayCopyStepMem σ ee (clipperListArraySlot k)
              (clipperListArrayDest k)
              (clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩) k) =
            clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩) (k + 1) :=
        clipperListArrayCopyStepMem_eq_copied (σ := σ) (ee := ee)
          (len := solcSlotWord σ ee ⟨11⟩) (n := k) hboundK
      exact ⟨_, _, by
        simpa [hn', hmem, clipperListArrayCopiedAw] using rdret⟩
  | succ m ih =>
      intro k hn k₀ C₀ hrd
      have hnNext : (solcSlotWord σ ee ⟨11⟩).toNat = (k + 1) + m + 1 := by
        omega
      have hboundSucc : 160 + 32 * (k + 1) < UInt256.size := by
        have hfree := clipperStorageWF_freePtr_lt hwfStorage
        omega
      have hboundK : 160 + 32 * k < UInt256.size := by omega
      have hdestStep := clipperListArrayDest_succ (n := k) hboundSucc
      have hend := clipperListArrayEndPtr_eq_dest_of_wf hwfStorage
      have hgt :
          UInt256.gt (clipperListArrayEndPtr (solcSlotWord σ ee ⟨11⟩))
            ((⟨32⟩ : UInt256) + clipperListArrayDest k) = ⟨1⟩ := by
        rw [hdestStep, hend]
        apply ugt_one
        rw [clipperListArrayDest_toNat (n := (solcSlotWord σ ee ⟨11⟩).toNat)
            (clipperStorageWF_freePtr_lt hwfStorage),
          clipperListArrayDest_toNat (n := k + 1) hboundSucc]
        omega
      have hcond :
          UInt256.gt (clipperListArrayEndPtr (solcSlotWord σ ee ⟨11⟩))
            ((⟨32⟩ : UInt256) + clipperListArrayDest k) ≠ ⟨0⟩ := by
        rw [hgt]
        native_decide
      obtain ⟨kNext, CNext, rdnextRaw⟩ :=
        clipperListStorageArrayLoopStepBack
          (R := R) (a := solcSlotWord σ ee ⟨11⟩) (b := (⟨11⟩ : UInt256))
          (base := clipperListArrayBasePtr) (ret := ret)
          hrd hwf h1870 hcond hov
      have hmem :
          clipperListArrayCopyStepMem σ ee (clipperListArraySlot k)
              (clipperListArrayDest k)
              (clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩) k) =
            clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩) (k + 1) :=
        clipperListArrayCopyStepMem_eq_copied (σ := σ) (ee := ee)
          (len := solcSlotWord σ ee ⟨11⟩) (n := k) hboundK
      have rdnext :
          RD code ee g s0 (⟨1870⟩ : UInt256)
            (clipperListArrayDest (k + 1) :: clipperListArraySlot (k + 1) ::
              clipperListArrayEndPtr (solcSlotWord σ ee ⟨11⟩) ::
              solcSlotWord σ ee ⟨11⟩ :: (⟨11⟩ : UInt256) :: clipperListArrayBasePtr ::
              (⟨96⟩ : UInt256) :: ret :: R)
            (clipperListArrayCopiedMem σ ee (solcSlotWord σ ee ⟨11⟩) (k + 1))
            (clipperListArrayCopiedAw (k + 1)) rdata (cA, σ) kNext CNext := by
        simpa [hdestStep, hmem, clipperListArrayCopiedAw, clipperListArraySlot] using rdnextRaw
      exact ih (k + 1) hnNext kNext CNext rdnext

end Benchmarks.Dss.Clipper
