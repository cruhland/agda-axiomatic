open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.MultiplicationDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.Multiplication.BaseDefn PA
  using (MB)
open import net.cruhland.models.Integers.NatPair.Multiplication.PropertiesDefn
  PA using (MP)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)

Z* : Multiplication ZB Z+ Z- ZS
Z* = record { MB = MB ; MP = MP }
