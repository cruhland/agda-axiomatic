open import net.cruhland.axioms.NewOrd using (_≤_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
open import net.cruhland.axioms.Sign using (Positive)

module net.cruhland.axioms.Peano.NewOrd.LessThan.PosDiffDecl
  (PB : PeanoBase)
  (PS : ℕSign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  where

open PeanoBase PB using (ℕ)
private module ℕ≤ = LteBase LTEB

record _≤⁺_ (n m : ℕ) : Set where
  constructor ≤⁺-intro
  field
    ≤⁺-elim-n≤m : n ≤ m
    ≤⁺-elim-d⁺ : Positive (ℕ≤.≤-diff ≤⁺-elim-n≤m)

open _≤⁺_ public using (≤⁺-elim-d⁺; ≤⁺-elim-n≤m)
