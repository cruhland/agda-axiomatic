module net.cruhland.axiomatic.Peano.Exponentiation where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import net.cruhland.axiomatic.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axiomatic.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axiomatic.Peano.Multiplication
  using () renaming (Multiplication to PeanoMultiplication)

record Exponentiation
    (PB : PeanoBase)
    (PA : PeanoAddition PB)
    (PM : PeanoMultiplication PB PA) : Set where
  open PeanoBase PB
  open PeanoMultiplication PM

  infixr 8 _^_

  field
    _^_ : ℕ → ℕ → ℕ
    ^-zeroᴿ : ∀ {n} → n ^ zero ≡ step zero
    ^-stepᴿ : ∀ {n m} → n ^ step m ≡ n ^ m * n
