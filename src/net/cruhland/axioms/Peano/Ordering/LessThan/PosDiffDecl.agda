open import net.cruhland.axioms.Ordering using (_≤_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
import net.cruhland.axioms.Sign as S

module net.cruhland.axioms.Peano.Ordering.LessThan.PosDiffDecl
  (PB : PeanoBase)
  (PS : ℕSign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  where

open PeanoBase PB using (ℕ)
import net.cruhland.axioms.Peano.Literals PB as ℕL
private
  module ℕ≤ = LteBase LTEB

record _≤⁺_ (n m : ℕ) : Set where
  constructor ≤⁺-intro
  field
    ≤⁺-elim-n≤m : n ≤ m
    ≤⁺-elim-d⁺ : S.Positive (ℕ≤.≤-diff ≤⁺-elim-n≤m)

open _≤⁺_ public using (≤⁺-elim-d⁺; ≤⁺-elim-n≤m)
