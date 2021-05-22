open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Sign.PropertiesDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)
import net.cruhland.models.Integers.NatPair.Sign.PropertiesImpl PA as SP
open import net.cruhland.models.Integers.NatPair.Sign.BaseDefn PA using (SB)

open import net.cruhland.axioms.Integers.Sign.PropertiesDecl PA ZB ZP Z+ Z-
  using (SignProperties)

SP : SignProperties SB
SP = record { SP }
