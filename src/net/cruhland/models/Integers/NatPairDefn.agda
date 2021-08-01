open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPairDefn (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers PA using (Integers)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (ZA)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.MultiplicationDefn PA
  using (ZM)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (ZN)
open import net.cruhland.models.Integers.NatPair.OrderingDefn PA using (ZO)
open import net.cruhland.models.Integers.NatPair.SignDefn PA using (ZS)

integers : Integers
integers = record
  { ZA = ZA
  ; ZB = ZB
  ; ZM = ZM
  ; ZN = ZN
  ; ZO = ZO
  ; ZS = ZS
  }
