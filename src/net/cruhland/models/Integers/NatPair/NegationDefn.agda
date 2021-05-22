open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.NegationDefn
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.Negation.BaseDefn PA using (NB)
open import net.cruhland.models.Integers.NatPair.Negation.PropertiesDefn PA
  using (NP)
open import net.cruhland.models.Integers.NatPair.PropertiesDefn PA using (ZP)

Z- : Negation ZB ZP Z+
Z- = record { NB = NB ; NP = NP }
