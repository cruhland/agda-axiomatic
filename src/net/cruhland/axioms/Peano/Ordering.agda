import net.cruhland.axioms.Eq as Eq
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.axioms.Sign using (Positivity)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Ordering
    (PB : PeanoBase) (PS : Sign PB) (PA : PeanoAddition PB PS) where

open PeanoBase PB using (ℕ)
import net.cruhland.axioms.Peano.Literals PB as ℕLit

-- Export contents of all child modules
open import net.cruhland.axioms.Peano.Ordering.LessThan PB PS PA public
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual PB PS PA public

greater-zero-positivity : Positivity 0
greater-zero-positivity =
  record { Positive = _> 0 ; nonzero = Eq.sym ∘ _<_.n≄m }
