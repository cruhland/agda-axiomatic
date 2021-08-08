import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Ordering as Ord using (_≤_; _<_)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseDecl
  using (LteBase)
open import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.PropertiesDecl
  using (LteProperties)
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_; contrapositive; no; yes)

module net.cruhland.axioms.Peano.Ordering.LessThan.BaseImplNeq
  (PB : PeanoBase)
  (PS : ℕSign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTEP : LteProperties PB PS PA LTEB)
  where

private module ℕ where
  open Addition PA public
  open LteBase LTEB public
  open LteProperties LTEP public
  open ℕSign PS public
  open PeanoBase PB public
  open import net.cruhland.axioms.Peano.Inspect PB public
  open import net.cruhland.axioms.Peano.Literals PB public

open ℕ using (ℕ)
open import net.cruhland.axioms.Peano.Ordering.LessThan.NeqDecl PB PS PA LTEB
  as ND using (_≤≄_)

instance
  lessThan : Ord.LessThan ℕ
  lessThan = Ord.lessThan _≤≄_

<-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n ≤≄ m
<-intro-≤≄ = ND.≤≄-intro

<-intro-≤pd : {n m : ℕ} (n≤m : n ≤ m) → S.Positive (ℕ.≤-diff n≤m) → n < m
<-intro-≤pd n≤m pos[d] =
  let d = ℕ.≤-diff n≤m
      d≄0 = S.pos≄0 pos[d]
      n+d≃m = ℕ.≤-elim-diff n≤m
      n≄m = contrapositive (AA.eq→idᴿ n+d≃m) d≄0
   in <-intro-≤≄ n≤m n≄m

<-elim-≤ : {n m : ℕ} → n ≤≄ m → n ≤ m
<-elim-≤ = ND.≤≄-elim-≤

<-elim-≄ : {n m : ℕ} → n ≤≄ m → n ≄ m
<-elim-≄ = ND.≤≄-elim-≄

<-diff : {n m : ℕ} → n < m → ℕ
<-diff n<m = ℕ.≤-diff (<-elim-≤ n<m)

<-diff-from-≤-diff :
  {n m : ℕ} (n<m : n < m) → <-diff n<m ≃ ℕ.≤-diff (<-elim-≤ n<m)
<-diff-from-≤-diff n<m = Eq.refl

<-intro-diff : {n m d : ℕ} → S.Positive d → n + d ≃ m → n < m
<-intro-diff pd n+d≃m =
  let n≤m = ℕ.≤-intro-diff n+d≃m
      d≃d[n≤m] = Eq.sym (ℕ.intro-diff-id n+d≃m)
   in <-intro-≤pd n≤m (AA.subst₁ d≃d[n≤m] pd)

<-elim-diff : {n m : ℕ} (n<m : n < m) → n + <-diff n<m ≃ m
<-elim-diff n<m = ℕ.≤-elim-diff (<-elim-≤ n<m)

<-diff-pos : {n m : ℕ} (n<m : n < m) → S.Positive (<-diff n<m)
<-diff-pos {n} {m} n<m with <-diff n<m ≃? 0
... | yes d≃0 =
  let n≃m =
        begin
          n
        ≃˘⟨ AA.ident ⟩
          n + 0
        ≃˘⟨ AA.subst₂ d≃0 ⟩
          n + <-diff n<m
        ≃⟨ <-elim-diff n<m ⟩
          m
        ∎
      n≄m = <-elim-≄ n<m
   in n≃m ↯ n≄m
... | no d≄0 =
  ℕ.Pos-intro-≄0 d≄0
