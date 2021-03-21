open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.AddDecl
  (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where

open PeanoBase PB using (ℕ)

infix 4 _+d≃_
record _+d≃_ (n m : ℕ) : Set where
  constructor +d≃-intro
  field
    {d} : ℕ
    +d≃-elim : n + d ≃ m

open _+d≃_ public using (+d≃-elim) renaming (d to diff)
