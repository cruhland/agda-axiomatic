open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals
  (PA : PeanoArithmetic) (Z : Integers PA) where

-- Export contents of child modules
open import net.cruhland.models.Rationals.Addition PA Z public
open import net.cruhland.models.Rationals.Base PA Z public
open import net.cruhland.models.Rationals.Equality PA Z public
open import net.cruhland.models.Rationals.Multiplication PA Z public
open import net.cruhland.models.Rationals.Negation PA Z public
open import net.cruhland.models.Rationals.Ordering PA Z public
open import net.cruhland.models.Rationals.Reciprocal PA Z public
