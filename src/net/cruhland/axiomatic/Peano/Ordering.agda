open import Relation.Binary.PropositionalEquality using (_≡_)
open import net.cruhland.axiomatic.Logic using (LogicBundle)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Ordering
  (LB : LogicBundle)
  (PB : PeanoBundle LB) where
  open LogicBundle LB
  open PeanoBundle PB
  open import net.cruhland.axiomatic.Peano.Addition LB PB

  _≤_ : ℕ → ℕ → Set
  n ≤ m = Σ ℕ (λ a → n + a ≡ m)

  _<_ : ℕ → ℕ → Set
  n < m = n ≤ m ∧ n ≢ m

  _≥_ : ℕ → ℕ → Set
  m ≥ n = n ≤ m

  _>_ : ℕ → ℕ → Set
  m > n = n < m

  infix 4 _≤_ _≥_ _<_ _>_
