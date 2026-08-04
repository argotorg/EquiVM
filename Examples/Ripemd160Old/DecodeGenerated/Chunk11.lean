import Examples.Ripemd160Old.DecodeGenerated.Chunk10

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes11 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1690⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1691⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1692⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1693⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1694⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1695⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨1697⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1698⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1699⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1700⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1701⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1702⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1705⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1706⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1707⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1708⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1709⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1710⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1711⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1712⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1713⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1714⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1716⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1717⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1718⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1719⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1720⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1721⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1724⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1725⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1726⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1727⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1728⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1729⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1730⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1731⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1732⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1733⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨1735⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1736⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1737⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1738⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1739⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1740⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1743⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1744⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1745⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1746⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1747⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1748⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1749⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1750⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1751⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1752⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨1754⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1755⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1756⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1757⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1758⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1759⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1762⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1763⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1764⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1765⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1766⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1767⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1768⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1769⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1770⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1771⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨1773⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1774⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1775⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1776⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1777⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1778⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1781⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1782⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1783⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1784⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1785⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1786⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1787⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1788⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1789⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1790⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1792⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1793⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1794⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1795⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1796⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1797⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1800⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1801⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1802⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1803⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1804⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1805⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1806⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1807⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none))
]

private theorem generatedDecodes11_correct : ∀ i : Fin generatedDecodes11.size,
    decode runtimeBytecode generatedDecodes11[i].1 = generatedDecodes11[i].2 := by
  native_decide

theorem decode_1690 : decode runtimeBytecode ⟨1690⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨0, by decide⟩
theorem decode_1691 : decode runtimeBytecode ⟨1691⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨1, by decide⟩
theorem decode_1692 : decode runtimeBytecode ⟨1692⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨2, by decide⟩
theorem decode_1693 : decode runtimeBytecode ⟨1693⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨3, by decide⟩
theorem decode_1694 : decode runtimeBytecode ⟨1694⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨4, by decide⟩
theorem decode_1695 : decode runtimeBytecode ⟨1695⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨5, by decide⟩
theorem decode_1697 : decode runtimeBytecode ⟨1697⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨6, by decide⟩
theorem decode_1698 : decode runtimeBytecode ⟨1698⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨7, by decide⟩
theorem decode_1699 : decode runtimeBytecode ⟨1699⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨8, by decide⟩
theorem decode_1700 : decode runtimeBytecode ⟨1700⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨9, by decide⟩
theorem decode_1701 : decode runtimeBytecode ⟨1701⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨10, by decide⟩
theorem decode_1702 : decode runtimeBytecode ⟨1702⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨11, by decide⟩
theorem decode_1705 : decode runtimeBytecode ⟨1705⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨12, by decide⟩
theorem decode_1706 : decode runtimeBytecode ⟨1706⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨13, by decide⟩
theorem decode_1707 : decode runtimeBytecode ⟨1707⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨14, by decide⟩
theorem decode_1708 : decode runtimeBytecode ⟨1708⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨15, by decide⟩
theorem decode_1709 : decode runtimeBytecode ⟨1709⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨16, by decide⟩
theorem decode_1710 : decode runtimeBytecode ⟨1710⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨17, by decide⟩
theorem decode_1711 : decode runtimeBytecode ⟨1711⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨18, by decide⟩
theorem decode_1712 : decode runtimeBytecode ⟨1712⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨19, by decide⟩
theorem decode_1713 : decode runtimeBytecode ⟨1713⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨20, by decide⟩
theorem decode_1714 : decode runtimeBytecode ⟨1714⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨21, by decide⟩
theorem decode_1716 : decode runtimeBytecode ⟨1716⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨22, by decide⟩
theorem decode_1717 : decode runtimeBytecode ⟨1717⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨23, by decide⟩
theorem decode_1718 : decode runtimeBytecode ⟨1718⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨24, by decide⟩
theorem decode_1719 : decode runtimeBytecode ⟨1719⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨25, by decide⟩
theorem decode_1720 : decode runtimeBytecode ⟨1720⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨26, by decide⟩
theorem decode_1721 : decode runtimeBytecode ⟨1721⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨27, by decide⟩
theorem decode_1724 : decode runtimeBytecode ⟨1724⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨28, by decide⟩
theorem decode_1725 : decode runtimeBytecode ⟨1725⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨29, by decide⟩
theorem decode_1726 : decode runtimeBytecode ⟨1726⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨30, by decide⟩
theorem decode_1727 : decode runtimeBytecode ⟨1727⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨31, by decide⟩
theorem decode_1728 : decode runtimeBytecode ⟨1728⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨32, by decide⟩
theorem decode_1729 : decode runtimeBytecode ⟨1729⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨33, by decide⟩
theorem decode_1730 : decode runtimeBytecode ⟨1730⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨34, by decide⟩
theorem decode_1731 : decode runtimeBytecode ⟨1731⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨35, by decide⟩
theorem decode_1732 : decode runtimeBytecode ⟨1732⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨36, by decide⟩
theorem decode_1733 : decode runtimeBytecode ⟨1733⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨37, by decide⟩
theorem decode_1735 : decode runtimeBytecode ⟨1735⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨38, by decide⟩
theorem decode_1736 : decode runtimeBytecode ⟨1736⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨39, by decide⟩
theorem decode_1737 : decode runtimeBytecode ⟨1737⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨40, by decide⟩
theorem decode_1738 : decode runtimeBytecode ⟨1738⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨41, by decide⟩
theorem decode_1739 : decode runtimeBytecode ⟨1739⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨42, by decide⟩
theorem decode_1740 : decode runtimeBytecode ⟨1740⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨43, by decide⟩
theorem decode_1743 : decode runtimeBytecode ⟨1743⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨44, by decide⟩
theorem decode_1744 : decode runtimeBytecode ⟨1744⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨45, by decide⟩
theorem decode_1745 : decode runtimeBytecode ⟨1745⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨46, by decide⟩
theorem decode_1746 : decode runtimeBytecode ⟨1746⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨47, by decide⟩
theorem decode_1747 : decode runtimeBytecode ⟨1747⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨48, by decide⟩
theorem decode_1748 : decode runtimeBytecode ⟨1748⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨49, by decide⟩
theorem decode_1749 : decode runtimeBytecode ⟨1749⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨50, by decide⟩
theorem decode_1750 : decode runtimeBytecode ⟨1750⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨51, by decide⟩
theorem decode_1751 : decode runtimeBytecode ⟨1751⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨52, by decide⟩
theorem decode_1752 : decode runtimeBytecode ⟨1752⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨53, by decide⟩
theorem decode_1754 : decode runtimeBytecode ⟨1754⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨54, by decide⟩
theorem decode_1755 : decode runtimeBytecode ⟨1755⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨55, by decide⟩
theorem decode_1756 : decode runtimeBytecode ⟨1756⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨56, by decide⟩
theorem decode_1757 : decode runtimeBytecode ⟨1757⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨57, by decide⟩
theorem decode_1758 : decode runtimeBytecode ⟨1758⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨58, by decide⟩
theorem decode_1759 : decode runtimeBytecode ⟨1759⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨59, by decide⟩
theorem decode_1762 : decode runtimeBytecode ⟨1762⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨60, by decide⟩
theorem decode_1763 : decode runtimeBytecode ⟨1763⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨61, by decide⟩
theorem decode_1764 : decode runtimeBytecode ⟨1764⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨62, by decide⟩
theorem decode_1765 : decode runtimeBytecode ⟨1765⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨63, by decide⟩
theorem decode_1766 : decode runtimeBytecode ⟨1766⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨64, by decide⟩
theorem decode_1767 : decode runtimeBytecode ⟨1767⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨65, by decide⟩
theorem decode_1768 : decode runtimeBytecode ⟨1768⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨66, by decide⟩
theorem decode_1769 : decode runtimeBytecode ⟨1769⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨67, by decide⟩
theorem decode_1770 : decode runtimeBytecode ⟨1770⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨68, by decide⟩
theorem decode_1771 : decode runtimeBytecode ⟨1771⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨69, by decide⟩
theorem decode_1773 : decode runtimeBytecode ⟨1773⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨70, by decide⟩
theorem decode_1774 : decode runtimeBytecode ⟨1774⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨71, by decide⟩
theorem decode_1775 : decode runtimeBytecode ⟨1775⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨72, by decide⟩
theorem decode_1776 : decode runtimeBytecode ⟨1776⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨73, by decide⟩
theorem decode_1777 : decode runtimeBytecode ⟨1777⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨74, by decide⟩
theorem decode_1778 : decode runtimeBytecode ⟨1778⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨75, by decide⟩
theorem decode_1781 : decode runtimeBytecode ⟨1781⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨76, by decide⟩
theorem decode_1782 : decode runtimeBytecode ⟨1782⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨77, by decide⟩
theorem decode_1783 : decode runtimeBytecode ⟨1783⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨78, by decide⟩
theorem decode_1784 : decode runtimeBytecode ⟨1784⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨79, by decide⟩
theorem decode_1785 : decode runtimeBytecode ⟨1785⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨80, by decide⟩
theorem decode_1786 : decode runtimeBytecode ⟨1786⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨81, by decide⟩
theorem decode_1787 : decode runtimeBytecode ⟨1787⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨82, by decide⟩
theorem decode_1788 : decode runtimeBytecode ⟨1788⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨83, by decide⟩
theorem decode_1789 : decode runtimeBytecode ⟨1789⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨84, by decide⟩
theorem decode_1790 : decode runtimeBytecode ⟨1790⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨85, by decide⟩
theorem decode_1792 : decode runtimeBytecode ⟨1792⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨86, by decide⟩
theorem decode_1793 : decode runtimeBytecode ⟨1793⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨87, by decide⟩
theorem decode_1794 : decode runtimeBytecode ⟨1794⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨88, by decide⟩
theorem decode_1795 : decode runtimeBytecode ⟨1795⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨89, by decide⟩
theorem decode_1796 : decode runtimeBytecode ⟨1796⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨90, by decide⟩
theorem decode_1797 : decode runtimeBytecode ⟨1797⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨91, by decide⟩
theorem decode_1800 : decode runtimeBytecode ⟨1800⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨92, by decide⟩
theorem decode_1801 : decode runtimeBytecode ⟨1801⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨93, by decide⟩
theorem decode_1802 : decode runtimeBytecode ⟨1802⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨94, by decide⟩
theorem decode_1803 : decode runtimeBytecode ⟨1803⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨95, by decide⟩
theorem decode_1804 : decode runtimeBytecode ⟨1804⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨96, by decide⟩
theorem decode_1805 : decode runtimeBytecode ⟨1805⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨97, by decide⟩
theorem decode_1806 : decode runtimeBytecode ⟨1806⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨98, by decide⟩
theorem decode_1807 : decode runtimeBytecode ⟨1807⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes11] using generatedDecodes11_correct ⟨99, by decide⟩

end Ripemd160Old
