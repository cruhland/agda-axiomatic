module net.cruhland.axioms.Peano.Exponentiation where

open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators as Op using (_*_; _^_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Multiplication using (Multiplication)
open import net.cruhland.axioms.Peano.NewOrd using (Ordering)
open import net.cruhland.axioms.Peano.Sign using (Sign)

record Exponentiation
    (PB : PeanoBase)
    (PS : Sign PB)
    (PA : Addition PB PS)
    (PO : Ordering PB PS PA)
    (PM : Multiplication PB PS PA PO) : Set where
  open PeanoBase PB using (ℕ; step; zero)

  field
    {{caret}} : Op.Caret ℕ
    ^-zeroᴿ : ∀ {n} → n ^ zero ≃ step zero
    ^-stepᴿ : ∀ {n m} → n ^ step m ≃ n ^ m * n
