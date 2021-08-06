open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.SignDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.SignDecl PA Z using (Sign)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
import net.cruhland.models.Rationals.IntPair.SignImpl PA Z as QS

QS : Sign QB
QS = record { QS }
