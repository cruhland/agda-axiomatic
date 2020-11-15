open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals (PA : PeanoArithmetic) where

-- Export contents of child modules
open import net.cruhland.models.Rationals.Addition PA public
open import net.cruhland.models.Rationals.Base PA public
open import net.cruhland.models.Rationals.Equality PA public
open import net.cruhland.models.Rationals.Multiplication PA public
open import net.cruhland.models.Rationals.Negation PA public
open import net.cruhland.models.Rationals.Ordering PA public
open import net.cruhland.models.Rationals.Reciprocal PA public
