open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.SignImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.models.Rationals.IntPair.DivisionDefn PA Z using (QD)
open import net.cruhland.models.Rationals.IntPair.NegationDefn PA Z using (QN)

-- Export all definitions from the default impl
open import net.cruhland.axioms.Rationals.SignDefaultImpl PA Z QB QA QN QD
  public
