open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Addition (PB : PeanoBundle) where
  open PeanoBundle PB

  _+_ : ℕ → ℕ → ℕ
  n + m = rec m succ n
