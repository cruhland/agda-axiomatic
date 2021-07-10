open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPairDefn
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals PA Z using (Rationals)
open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (Q+)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

rationals : Rationals
rationals = record { QB = QB ; Q+ = Q+ }
