open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.Multiplication.PropertiesDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.Multiplication.BaseDefn PA
  using (MB)
import net.cruhland.models.Integers.NatPair.Multiplication.PropertiesImpl PA
  as MP
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)

open import net.cruhland.axioms.Integers.Multiplication.PropertiesDecl
  PA ZB ZP Z+ Z- using (MultiplicationProperties)

MP : MultiplicationProperties MB
MP = record { MP }
