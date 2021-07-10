open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.BaseDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z as QB

QB : Base
QB = record { QB }
