open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.NegationDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)
import net.cruhland.models.Rationals.IntPair.NegationImpl PA Z as Q-
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

Q- : Negation QB
Q- = record { Q- }
