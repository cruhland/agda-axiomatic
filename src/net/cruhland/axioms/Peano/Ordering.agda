open import net.cruhland.axioms.Eq using (¬sym)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.axioms.Sign using (Positivity)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Ordering
    (PB : PeanoBase) (PA : PeanoAddition PB) (PS : Sign PB PA) where

open PeanoBase PB using (ℕ)
import net.cruhland.axioms.Peano.Literals PB as ℕLit

-- Export contents of all child modules
open import net.cruhland.axioms.Peano.Ordering.LessThan PB PA PS public
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual PB PA PS public

greater-zero-positivity : Positivity 0
greater-zero-positivity = record { Positive = _> 0 ; nonzero = ¬sym ∘ _<_.n≄m }
