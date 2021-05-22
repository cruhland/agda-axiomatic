open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Sign.BaseDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)
import net.cruhland.models.Integers.NatPair.Sign.BaseImpl PA as BaseImpl
import net.cruhland.models.Integers.NatPair.Sign.BaseImplLt PA as BaseImplLt
import net.cruhland.models.Integers.NatPair.Sign.BaseImplNat PA as BaseImplNat

open import net.cruhland.axioms.Integers.Sign.BaseDecl PA ZB ZP Z+ Z-
  using (SignBase)

-- Confirm all impls conform to the decl
baseImplLt : SignBase
baseImplLt = record { BaseImplLt }

baseImplNat : SignBase
baseImplNat = record { BaseImplNat }

-- Designate the default impl
SB : SignBase
SB = record { BaseImpl }
