open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.NewOrd using
  (_≤_; _<_; LessThan; LessThanOrEqual)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

open PeanoBase PB using (ℕ)

record LtBase : Set₁ where
  field
    {{lessThan}} : LessThan ℕ
    <-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n < m
    <-elim-≤ : {n m : ℕ} → n < m → n ≤ m
    <-elim-≄ : {n m : ℕ} → n < m → n ≄ m
