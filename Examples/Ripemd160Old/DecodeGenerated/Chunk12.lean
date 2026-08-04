import Examples.Ripemd160Old.DecodeGenerated.Chunk11

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes12 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1808⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1809⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨1811⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1812⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1813⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1814⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1815⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1816⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1819⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1820⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1821⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1822⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1823⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1824⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1825⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1826⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1827⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1828⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨1830⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1831⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1832⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1833⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1834⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1835⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1838⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1839⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1840⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1841⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1842⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1843⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1844⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1845⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1846⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1847⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨1849⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1850⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1851⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1852⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1853⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1854⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1857⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1858⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1859⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1860⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1861⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1862⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1863⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1864⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1865⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1866⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨1868⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1869⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1870⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1871⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1872⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1873⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1876⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1877⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1878⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1879⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨1881⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1882⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1883⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨1884⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1885⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨1886⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1887⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨1888⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1889⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2304⟩, 2))),
  (⟨1892⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1893⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1894⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨1896⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1897⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2285⟩, 2))),
  (⟨1900⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1901⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1902⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨1904⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1905⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2266⟩, 2))),
  (⟨1908⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1909⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1910⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨1912⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1913⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2247⟩, 2))),
  (⟨1916⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1917⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1918⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨1920⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1921⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2228⟩, 2))),
  (⟨1924⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1925⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1926⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨1928⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1929⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2209⟩, 2))),
  (⟨1932⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1933⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1934⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨1936⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1937⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2190⟩, 2))),
  (⟨1940⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none))
]

private theorem generatedDecodes12_correct : ∀ i : Fin generatedDecodes12.size,
    decode runtimeBytecode generatedDecodes12[i].1 = generatedDecodes12[i].2 := by
  native_decide

theorem decode_1808 : decode runtimeBytecode ⟨1808⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨0, by decide⟩
theorem decode_1809 : decode runtimeBytecode ⟨1809⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨1, by decide⟩
theorem decode_1811 : decode runtimeBytecode ⟨1811⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨2, by decide⟩
theorem decode_1812 : decode runtimeBytecode ⟨1812⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨3, by decide⟩
theorem decode_1813 : decode runtimeBytecode ⟨1813⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨4, by decide⟩
theorem decode_1814 : decode runtimeBytecode ⟨1814⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨5, by decide⟩
theorem decode_1815 : decode runtimeBytecode ⟨1815⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨6, by decide⟩
theorem decode_1816 : decode runtimeBytecode ⟨1816⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨7, by decide⟩
theorem decode_1819 : decode runtimeBytecode ⟨1819⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨8, by decide⟩
theorem decode_1820 : decode runtimeBytecode ⟨1820⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨9, by decide⟩
theorem decode_1821 : decode runtimeBytecode ⟨1821⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨10, by decide⟩
theorem decode_1822 : decode runtimeBytecode ⟨1822⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨11, by decide⟩
theorem decode_1823 : decode runtimeBytecode ⟨1823⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨12, by decide⟩
theorem decode_1824 : decode runtimeBytecode ⟨1824⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨13, by decide⟩
theorem decode_1825 : decode runtimeBytecode ⟨1825⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨14, by decide⟩
theorem decode_1826 : decode runtimeBytecode ⟨1826⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨15, by decide⟩
theorem decode_1827 : decode runtimeBytecode ⟨1827⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨16, by decide⟩
theorem decode_1828 : decode runtimeBytecode ⟨1828⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨17, by decide⟩
theorem decode_1830 : decode runtimeBytecode ⟨1830⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨18, by decide⟩
theorem decode_1831 : decode runtimeBytecode ⟨1831⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨19, by decide⟩
theorem decode_1832 : decode runtimeBytecode ⟨1832⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨20, by decide⟩
theorem decode_1833 : decode runtimeBytecode ⟨1833⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨21, by decide⟩
theorem decode_1834 : decode runtimeBytecode ⟨1834⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨22, by decide⟩
theorem decode_1835 : decode runtimeBytecode ⟨1835⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨23, by decide⟩
theorem decode_1838 : decode runtimeBytecode ⟨1838⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨24, by decide⟩
theorem decode_1839 : decode runtimeBytecode ⟨1839⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨25, by decide⟩
theorem decode_1840 : decode runtimeBytecode ⟨1840⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨26, by decide⟩
theorem decode_1841 : decode runtimeBytecode ⟨1841⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨27, by decide⟩
theorem decode_1842 : decode runtimeBytecode ⟨1842⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨28, by decide⟩
theorem decode_1843 : decode runtimeBytecode ⟨1843⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨29, by decide⟩
theorem decode_1844 : decode runtimeBytecode ⟨1844⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨30, by decide⟩
theorem decode_1845 : decode runtimeBytecode ⟨1845⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨31, by decide⟩
theorem decode_1846 : decode runtimeBytecode ⟨1846⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨32, by decide⟩
theorem decode_1847 : decode runtimeBytecode ⟨1847⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨33, by decide⟩
theorem decode_1849 : decode runtimeBytecode ⟨1849⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨34, by decide⟩
theorem decode_1850 : decode runtimeBytecode ⟨1850⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨35, by decide⟩
theorem decode_1851 : decode runtimeBytecode ⟨1851⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨36, by decide⟩
theorem decode_1852 : decode runtimeBytecode ⟨1852⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨37, by decide⟩
theorem decode_1853 : decode runtimeBytecode ⟨1853⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨38, by decide⟩
theorem decode_1854 : decode runtimeBytecode ⟨1854⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨39, by decide⟩
theorem decode_1857 : decode runtimeBytecode ⟨1857⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨40, by decide⟩
theorem decode_1858 : decode runtimeBytecode ⟨1858⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨41, by decide⟩
theorem decode_1859 : decode runtimeBytecode ⟨1859⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨42, by decide⟩
theorem decode_1860 : decode runtimeBytecode ⟨1860⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨43, by decide⟩
theorem decode_1861 : decode runtimeBytecode ⟨1861⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨44, by decide⟩
theorem decode_1862 : decode runtimeBytecode ⟨1862⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨45, by decide⟩
theorem decode_1863 : decode runtimeBytecode ⟨1863⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨46, by decide⟩
theorem decode_1864 : decode runtimeBytecode ⟨1864⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨47, by decide⟩
theorem decode_1865 : decode runtimeBytecode ⟨1865⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨48, by decide⟩
theorem decode_1866 : decode runtimeBytecode ⟨1866⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨49, by decide⟩
theorem decode_1868 : decode runtimeBytecode ⟨1868⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨50, by decide⟩
theorem decode_1869 : decode runtimeBytecode ⟨1869⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨51, by decide⟩
theorem decode_1870 : decode runtimeBytecode ⟨1870⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨52, by decide⟩
theorem decode_1871 : decode runtimeBytecode ⟨1871⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨53, by decide⟩
theorem decode_1872 : decode runtimeBytecode ⟨1872⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨54, by decide⟩
theorem decode_1873 : decode runtimeBytecode ⟨1873⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨55, by decide⟩
theorem decode_1876 : decode runtimeBytecode ⟨1876⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨56, by decide⟩
theorem decode_1877 : decode runtimeBytecode ⟨1877⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨57, by decide⟩
theorem decode_1878 : decode runtimeBytecode ⟨1878⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨58, by decide⟩
theorem decode_1879 : decode runtimeBytecode ⟨1879⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨59, by decide⟩
theorem decode_1881 : decode runtimeBytecode ⟨1881⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨60, by decide⟩
theorem decode_1882 : decode runtimeBytecode ⟨1882⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨61, by decide⟩
theorem decode_1883 : decode runtimeBytecode ⟨1883⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨62, by decide⟩
theorem decode_1884 : decode runtimeBytecode ⟨1884⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨63, by decide⟩
theorem decode_1885 : decode runtimeBytecode ⟨1885⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨64, by decide⟩
theorem decode_1886 : decode runtimeBytecode ⟨1886⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨65, by decide⟩
theorem decode_1887 : decode runtimeBytecode ⟨1887⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨66, by decide⟩
theorem decode_1888 : decode runtimeBytecode ⟨1888⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨67, by decide⟩
theorem decode_1889 : decode runtimeBytecode ⟨1889⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2304⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨68, by decide⟩
theorem decode_1892 : decode runtimeBytecode ⟨1892⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨69, by decide⟩
theorem decode_1893 : decode runtimeBytecode ⟨1893⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨70, by decide⟩
theorem decode_1894 : decode runtimeBytecode ⟨1894⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨71, by decide⟩
theorem decode_1896 : decode runtimeBytecode ⟨1896⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨72, by decide⟩
theorem decode_1897 : decode runtimeBytecode ⟨1897⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2285⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨73, by decide⟩
theorem decode_1900 : decode runtimeBytecode ⟨1900⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨74, by decide⟩
theorem decode_1901 : decode runtimeBytecode ⟨1901⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨75, by decide⟩
theorem decode_1902 : decode runtimeBytecode ⟨1902⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨76, by decide⟩
theorem decode_1904 : decode runtimeBytecode ⟨1904⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨77, by decide⟩
theorem decode_1905 : decode runtimeBytecode ⟨1905⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2266⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨78, by decide⟩
theorem decode_1908 : decode runtimeBytecode ⟨1908⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨79, by decide⟩
theorem decode_1909 : decode runtimeBytecode ⟨1909⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨80, by decide⟩
theorem decode_1910 : decode runtimeBytecode ⟨1910⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨81, by decide⟩
theorem decode_1912 : decode runtimeBytecode ⟨1912⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨82, by decide⟩
theorem decode_1913 : decode runtimeBytecode ⟨1913⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2247⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨83, by decide⟩
theorem decode_1916 : decode runtimeBytecode ⟨1916⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨84, by decide⟩
theorem decode_1917 : decode runtimeBytecode ⟨1917⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨85, by decide⟩
theorem decode_1918 : decode runtimeBytecode ⟨1918⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨86, by decide⟩
theorem decode_1920 : decode runtimeBytecode ⟨1920⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨87, by decide⟩
theorem decode_1921 : decode runtimeBytecode ⟨1921⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2228⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨88, by decide⟩
theorem decode_1924 : decode runtimeBytecode ⟨1924⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨89, by decide⟩
theorem decode_1925 : decode runtimeBytecode ⟨1925⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨90, by decide⟩
theorem decode_1926 : decode runtimeBytecode ⟨1926⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨91, by decide⟩
theorem decode_1928 : decode runtimeBytecode ⟨1928⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨92, by decide⟩
theorem decode_1929 : decode runtimeBytecode ⟨1929⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2209⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨93, by decide⟩
theorem decode_1932 : decode runtimeBytecode ⟨1932⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨94, by decide⟩
theorem decode_1933 : decode runtimeBytecode ⟨1933⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨95, by decide⟩
theorem decode_1934 : decode runtimeBytecode ⟨1934⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨96, by decide⟩
theorem decode_1936 : decode runtimeBytecode ⟨1936⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨97, by decide⟩
theorem decode_1937 : decode runtimeBytecode ⟨1937⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2190⟩, 2)) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨98, by decide⟩
theorem decode_1940 : decode runtimeBytecode ⟨1940⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes12] using generatedDecodes12_correct ⟨99, by decide⟩

end Ripemd160Old
