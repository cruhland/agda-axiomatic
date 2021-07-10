open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.AdditionDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
import net.cruhland.models.Rationals.IntPair.AdditionImpl PA Z as Q+
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

Q+ : Addition QB
Q+ = record { Q+ }
