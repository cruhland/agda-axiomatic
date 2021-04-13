open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.Ordering using (_≤_; LessThanOrEqual)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.Ordering.LessThan.NeqDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

open PeanoBase PB using (ℕ)

record _≤≄_ (n m : ℕ) : Set where
  constructor ≤≄-intro
  field
    ≤≄-elim-≤ : n ≤ m
    ≤≄-elim-≄ : n ≄ m

open _≤≄_ public using (≤≄-elim-≤; ≤≄-elim-≄)
