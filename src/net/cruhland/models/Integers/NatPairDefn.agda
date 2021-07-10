open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPairDefn (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers PA using (Integers)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.MultiplicationDefn PA
  using (Z*)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
open import net.cruhland.models.Integers.NatPair.OrderingDefn PA using (Z<)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)

integers : Integers
integers = record
  { ZB = ZB
  ; Z+ = Z+
  ; Z- = Z-
  ; ZS = ZS
  ; Z* = Z*
  ; Z< = Z<
  }