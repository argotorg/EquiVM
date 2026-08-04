import Examples.Ripemd160Old.DecodeGenerated.Chunk12

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes13 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1941⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1942⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨1944⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1945⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2171⟩, 2))),
  (⟨1948⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1949⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1950⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨1952⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1953⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2152⟩, 2))),
  (⟨1956⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1957⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1958⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨1960⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1961⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2133⟩, 2))),
  (⟨1964⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1965⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1966⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨1967⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1968⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2114⟩, 2))),
  (⟨1971⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1972⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1973⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨1975⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1976⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2095⟩, 2))),
  (⟨1979⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1980⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1981⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨1983⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1984⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2076⟩, 2))),
  (⟨1987⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1988⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1989⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨1991⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1992⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2057⟩, 2))),
  (⟨1995⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1996⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1997⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1999⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2000⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2038⟩, 2))),
  (⟨2003⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2004⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨2006⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2007⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2020⟩, 2))),
  (⟨2010⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2011⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2012⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2013⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2014⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2015⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨2016⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2))),
  (⟨2019⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2020⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2021⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2022⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2023⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2024⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2025⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2026⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2027⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨2029⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2030⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2031⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2032⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2033⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2034⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2))),
  (⟨2037⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2038⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2039⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2040⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2041⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2042⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2043⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2044⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2045⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2046⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨2048⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2049⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2050⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2051⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2052⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2053⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2))),
  (⟨2056⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2057⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2058⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2059⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2060⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2061⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2062⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2063⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2064⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2065⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨2067⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2068⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2069⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2070⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2071⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2072⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2))),
  (⟨2075⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2076⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2077⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes13_correct : ∀ i : Fin generatedDecodes13.size,
    decode runtimeBytecode generatedDecodes13[i].1 = generatedDecodes13[i].2 := by
  native_decide

theorem decode_1941 : decode runtimeBytecode ⟨1941⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨0, by decide⟩
theorem decode_1942 : decode runtimeBytecode ⟨1942⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨1, by decide⟩
theorem decode_1944 : decode runtimeBytecode ⟨1944⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨2, by decide⟩
theorem decode_1945 : decode runtimeBytecode ⟨1945⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2171⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨3, by decide⟩
theorem decode_1948 : decode runtimeBytecode ⟨1948⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨4, by decide⟩
theorem decode_1949 : decode runtimeBytecode ⟨1949⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨5, by decide⟩
theorem decode_1950 : decode runtimeBytecode ⟨1950⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨6, by decide⟩
theorem decode_1952 : decode runtimeBytecode ⟨1952⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨7, by decide⟩
theorem decode_1953 : decode runtimeBytecode ⟨1953⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2152⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨8, by decide⟩
theorem decode_1956 : decode runtimeBytecode ⟨1956⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨9, by decide⟩
theorem decode_1957 : decode runtimeBytecode ⟨1957⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨10, by decide⟩
theorem decode_1958 : decode runtimeBytecode ⟨1958⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨11, by decide⟩
theorem decode_1960 : decode runtimeBytecode ⟨1960⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨12, by decide⟩
theorem decode_1961 : decode runtimeBytecode ⟨1961⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2133⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨13, by decide⟩
theorem decode_1964 : decode runtimeBytecode ⟨1964⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨14, by decide⟩
theorem decode_1965 : decode runtimeBytecode ⟨1965⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨15, by decide⟩
theorem decode_1966 : decode runtimeBytecode ⟨1966⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨16, by decide⟩
theorem decode_1967 : decode runtimeBytecode ⟨1967⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨17, by decide⟩
theorem decode_1968 : decode runtimeBytecode ⟨1968⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2114⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨18, by decide⟩
theorem decode_1971 : decode runtimeBytecode ⟨1971⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨19, by decide⟩
theorem decode_1972 : decode runtimeBytecode ⟨1972⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨20, by decide⟩
theorem decode_1973 : decode runtimeBytecode ⟨1973⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨21, by decide⟩
theorem decode_1975 : decode runtimeBytecode ⟨1975⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨22, by decide⟩
theorem decode_1976 : decode runtimeBytecode ⟨1976⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2095⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨23, by decide⟩
theorem decode_1979 : decode runtimeBytecode ⟨1979⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨24, by decide⟩
theorem decode_1980 : decode runtimeBytecode ⟨1980⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨25, by decide⟩
theorem decode_1981 : decode runtimeBytecode ⟨1981⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨26, by decide⟩
theorem decode_1983 : decode runtimeBytecode ⟨1983⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨27, by decide⟩
theorem decode_1984 : decode runtimeBytecode ⟨1984⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2076⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨28, by decide⟩
theorem decode_1987 : decode runtimeBytecode ⟨1987⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨29, by decide⟩
theorem decode_1988 : decode runtimeBytecode ⟨1988⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨30, by decide⟩
theorem decode_1989 : decode runtimeBytecode ⟨1989⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨31, by decide⟩
theorem decode_1991 : decode runtimeBytecode ⟨1991⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨32, by decide⟩
theorem decode_1992 : decode runtimeBytecode ⟨1992⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2057⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨33, by decide⟩
theorem decode_1995 : decode runtimeBytecode ⟨1995⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨34, by decide⟩
theorem decode_1996 : decode runtimeBytecode ⟨1996⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨35, by decide⟩
theorem decode_1997 : decode runtimeBytecode ⟨1997⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨36, by decide⟩
theorem decode_1999 : decode runtimeBytecode ⟨1999⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨37, by decide⟩
theorem decode_2000 : decode runtimeBytecode ⟨2000⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2038⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨38, by decide⟩
theorem decode_2003 : decode runtimeBytecode ⟨2003⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨39, by decide⟩
theorem decode_2004 : decode runtimeBytecode ⟨2004⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨40, by decide⟩
theorem decode_2006 : decode runtimeBytecode ⟨2006⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨41, by decide⟩
theorem decode_2007 : decode runtimeBytecode ⟨2007⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2020⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨42, by decide⟩
theorem decode_2010 : decode runtimeBytecode ⟨2010⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨43, by decide⟩
theorem decode_2011 : decode runtimeBytecode ⟨2011⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨44, by decide⟩
theorem decode_2012 : decode runtimeBytecode ⟨2012⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨45, by decide⟩
theorem decode_2013 : decode runtimeBytecode ⟨2013⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨46, by decide⟩
theorem decode_2014 : decode runtimeBytecode ⟨2014⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨47, by decide⟩
theorem decode_2015 : decode runtimeBytecode ⟨2015⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨48, by decide⟩
theorem decode_2016 : decode runtimeBytecode ⟨2016⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨49, by decide⟩
theorem decode_2019 : decode runtimeBytecode ⟨2019⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨50, by decide⟩
theorem decode_2020 : decode runtimeBytecode ⟨2020⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨51, by decide⟩
theorem decode_2021 : decode runtimeBytecode ⟨2021⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨52, by decide⟩
theorem decode_2022 : decode runtimeBytecode ⟨2022⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨53, by decide⟩
theorem decode_2023 : decode runtimeBytecode ⟨2023⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨54, by decide⟩
theorem decode_2024 : decode runtimeBytecode ⟨2024⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨55, by decide⟩
theorem decode_2025 : decode runtimeBytecode ⟨2025⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨56, by decide⟩
theorem decode_2026 : decode runtimeBytecode ⟨2026⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨57, by decide⟩
theorem decode_2027 : decode runtimeBytecode ⟨2027⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨58, by decide⟩
theorem decode_2029 : decode runtimeBytecode ⟨2029⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨59, by decide⟩
theorem decode_2030 : decode runtimeBytecode ⟨2030⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨60, by decide⟩
theorem decode_2031 : decode runtimeBytecode ⟨2031⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨61, by decide⟩
theorem decode_2032 : decode runtimeBytecode ⟨2032⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨62, by decide⟩
theorem decode_2033 : decode runtimeBytecode ⟨2033⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨63, by decide⟩
theorem decode_2034 : decode runtimeBytecode ⟨2034⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨64, by decide⟩
theorem decode_2037 : decode runtimeBytecode ⟨2037⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨65, by decide⟩
theorem decode_2038 : decode runtimeBytecode ⟨2038⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨66, by decide⟩
theorem decode_2039 : decode runtimeBytecode ⟨2039⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨67, by decide⟩
theorem decode_2040 : decode runtimeBytecode ⟨2040⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨68, by decide⟩
theorem decode_2041 : decode runtimeBytecode ⟨2041⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨69, by decide⟩
theorem decode_2042 : decode runtimeBytecode ⟨2042⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨70, by decide⟩
theorem decode_2043 : decode runtimeBytecode ⟨2043⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨71, by decide⟩
theorem decode_2044 : decode runtimeBytecode ⟨2044⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨72, by decide⟩
theorem decode_2045 : decode runtimeBytecode ⟨2045⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨73, by decide⟩
theorem decode_2046 : decode runtimeBytecode ⟨2046⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨74, by decide⟩
theorem decode_2048 : decode runtimeBytecode ⟨2048⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨75, by decide⟩
theorem decode_2049 : decode runtimeBytecode ⟨2049⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨76, by decide⟩
theorem decode_2050 : decode runtimeBytecode ⟨2050⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨77, by decide⟩
theorem decode_2051 : decode runtimeBytecode ⟨2051⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨78, by decide⟩
theorem decode_2052 : decode runtimeBytecode ⟨2052⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨79, by decide⟩
theorem decode_2053 : decode runtimeBytecode ⟨2053⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨80, by decide⟩
theorem decode_2056 : decode runtimeBytecode ⟨2056⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨81, by decide⟩
theorem decode_2057 : decode runtimeBytecode ⟨2057⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨82, by decide⟩
theorem decode_2058 : decode runtimeBytecode ⟨2058⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨83, by decide⟩
theorem decode_2059 : decode runtimeBytecode ⟨2059⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨84, by decide⟩
theorem decode_2060 : decode runtimeBytecode ⟨2060⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨85, by decide⟩
theorem decode_2061 : decode runtimeBytecode ⟨2061⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨86, by decide⟩
theorem decode_2062 : decode runtimeBytecode ⟨2062⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨87, by decide⟩
theorem decode_2063 : decode runtimeBytecode ⟨2063⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨88, by decide⟩
theorem decode_2064 : decode runtimeBytecode ⟨2064⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨89, by decide⟩
theorem decode_2065 : decode runtimeBytecode ⟨2065⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨90, by decide⟩
theorem decode_2067 : decode runtimeBytecode ⟨2067⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨91, by decide⟩
theorem decode_2068 : decode runtimeBytecode ⟨2068⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨92, by decide⟩
theorem decode_2069 : decode runtimeBytecode ⟨2069⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨93, by decide⟩
theorem decode_2070 : decode runtimeBytecode ⟨2070⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨94, by decide⟩
theorem decode_2071 : decode runtimeBytecode ⟨2071⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨95, by decide⟩
theorem decode_2072 : decode runtimeBytecode ⟨2072⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2)) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨96, by decide⟩
theorem decode_2075 : decode runtimeBytecode ⟨2075⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨97, by decide⟩
theorem decode_2076 : decode runtimeBytecode ⟨2076⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨98, by decide⟩
theorem decode_2077 : decode runtimeBytecode ⟨2077⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes13] using generatedDecodes13_correct ⟨99, by decide⟩

end Ripemd160Old
