open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Ordering using
  (_≤_; _<_; LessThan; LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  as LteBaseDecl
open import net.cruhland.axioms.Peano.Sign using (Sign)
import net.cruhland.axioms.Sign as S

module net.cruhland.axioms.Peano.Ordering.LessThan.BaseDecl
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  where

open PeanoBase PB using (ℕ)
import net.cruhland.axioms.Peano.Literals PB as ℕL
open LteBaseDecl PB PS PA using (LteBase)

record LtBase (LTEB : LteBase) : Set₁ where
  private module ℕ≤ = LteBase LTEB

  field
    {{lessThan}} : LessThan ℕ

    <-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n < m
    <-intro-≤pd : {n m : ℕ} (n≤m : n ≤ m) → S.Positive (ℕ≤.≤-diff n≤m) → n < m

    <-elim-≤ : {n m : ℕ} → n < m → n ≤ m
    <-elim-≄ : {n m : ℕ} → n < m → n ≄ m

    <-diff : {n m : ℕ} → n < m → ℕ
    <-diff-pos : {n m : ℕ} (n<m : n < m) → S.Positive (<-diff n<m)
    <-diff-from-≤-diff :
      {n m : ℕ} (n<m : n < m) → <-diff n<m ≃ ℕ≤.≤-diff (<-elim-≤ n<m)
    <-intro-diff : {n m d : ℕ} → S.Positive d → n + d ≃ m → n < m
    <-elim-diff : {n m : ℕ} (n<m : n < m) → n + <-diff n<m ≃ m
