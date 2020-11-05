module net.cruhland.axioms.Peano.Exponentiation where

open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_*_)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Multiplication
  using () renaming (Multiplication to PeanoMultiplication)

record Exponentiation
    (PB : PeanoBase)
    (PA : PeanoAddition PB)
    (PM : PeanoMultiplication PB PA) : Set where
  open PeanoBase PB using (ℕ; step; zero)

  infixr 8 _^_

  field
    _^_ : ℕ → ℕ → ℕ
    ^-zeroᴿ : ∀ {n} → n ^ zero ≃ step zero
    ^-stepᴿ : ∀ {n m} → n ^ step m ≃ n ^ m * n
