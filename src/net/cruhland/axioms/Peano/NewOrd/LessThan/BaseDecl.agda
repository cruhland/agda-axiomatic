open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.NewOrd using
  (_≤_; _<_; LessThan; LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.axioms.Sign using (Positive)

module net.cruhland.axioms.Peano.NewOrd.LessThan.BaseDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

open PeanoBase PB using (ℕ)
private module ℕ≤ = LteBase LTEB

record LtBase : Set₁ where
  field
    {{lessThan}} : LessThan ℕ

    <-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n < m
    <-intro-≤pd : {n m : ℕ} (n≤m : n ≤ m) → Positive (ℕ≤.≤-diff n≤m) → n < m

    <-elim-≤ : {n m : ℕ} → n < m → n ≤ m
    <-elim-≄ : {n m : ℕ} → n < m → n ≄ m

    <-diff : {n m : ℕ} → n < m → ℕ
    <-diff-pos : {n m : ℕ} (n<m : n < m) → Positive (<-diff n<m)
    <-intro-diff : {n m d : ℕ} → Positive d → n + d ≃ m → n < m
    <-elim-diff : {n m : ℕ} (n<m : n < m) → n + <-diff n<m ≃ m
