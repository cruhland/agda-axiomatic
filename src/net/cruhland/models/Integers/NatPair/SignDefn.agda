open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.SignDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)
open import net.cruhland.models.Integers.NatPair.Sign.BaseDefn PA using (SB)
open import net.cruhland.models.Integers.NatPair.Sign.PropertiesDefn PA
  using (SP)

ZS : Sign ZB ZP Z+ Z-
ZS = record { SB = SB ; SP = SP }
