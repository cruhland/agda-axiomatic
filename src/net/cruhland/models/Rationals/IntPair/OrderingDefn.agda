open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.OrderingDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.OrderingDecl PA Z using (Ordering)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
import net.cruhland.models.Rationals.IntPair.OrderingImpl PA Z as QO

QO : Ordering QB
QO = record { QO }
