open import Function using (flip)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; sym)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_)

module net.cruhland.axioms.Peano.Ordering.LessThanOrEqual
  (PB : PeanoBase) (PA : PeanoAddition PB) where

module ℕ+ = PeanoAddition PA
open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕLit

infix 4 _≤_ _≥_ _≰_ _≱_

record _≤_ (n m : ℕ) : Set where
  constructor ≤-intro
  field
    d : ℕ
    n+d≃m : n + d ≃ m

_≰_ : ℕ → ℕ → Set
n ≰ m = ¬ (n ≤ m)

_≥_ = flip _≤_
_≱_ = flip _≰_

≤-refl : ∀ {n} → n ≤ n
≤-refl = record { d = 0 ; n+d≃m = AA.identᴿ }

n≤sn : ∀ {n} → n ≤ step n
n≤sn = record { d = 1 ; n+d≃m = sym ℕ+.sn≃n+1 }
