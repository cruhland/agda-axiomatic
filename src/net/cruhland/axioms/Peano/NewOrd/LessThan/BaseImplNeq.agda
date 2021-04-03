import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; _<_; LessThan)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl using
  (LteProperties)
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
open import net.cruhland.axioms.Sign as Sign using (Positive)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contra; no; yes)

module net.cruhland.axioms.Peano.NewOrd.LessThan.BaseImplNeq
  (PB : PeanoBase)
  (PS : ℕSign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTEP : LteProperties PB PS PA LTEB) where

private module ℕ+ = Addition PA
open PeanoBase PB using (ℕ)
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕL
private module ℕS = ℕSign PS
private module ℕ≤ = LteBase LTEB
private module ℕ≤P = LteProperties LTEP
open import net.cruhland.axioms.Peano.NewOrd.LessThan.NeqDecl PB PS PA LTEB
  as ND using (_≤≄_)

instance
  lessThan : LessThan ℕ
  lessThan = record { _<_ = _≤≄_ }

<-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n ≤≄ m
<-intro-≤≄ = ND.≤≄-intro

<-intro-≤pd : {n m : ℕ} (n≤m : n ≤ m) → Positive (ℕ≤.≤-diff n≤m) → n < m
<-intro-≤pd n≤m pd =
  let d = ℕ≤.≤-diff n≤m
      n+d≃m = ℕ≤.≤-elim-diff n≤m
      n≄m = λ n≃m → contra (AA.eq→idᴿ n+d≃m n≃m) (Sign.pos≄0 pd)
   in <-intro-≤≄ n≤m n≄m

<-elim-≤ : {n m : ℕ} → n ≤≄ m → n ≤ m
<-elim-≤ = ND.≤≄-elim-≤

<-elim-≄ : {n m : ℕ} → n ≤≄ m → n ≄ m
<-elim-≄ = ND.≤≄-elim-≄

<-diff : {n m : ℕ} → n < m → ℕ
<-diff n<m = ℕ≤.≤-diff (<-elim-≤ n<m)

<-diff-from-≤-diff :
  {n m : ℕ} (n<m : n < m) → <-diff n<m ≃ ℕ≤.≤-diff (<-elim-≤ n<m)
<-diff-from-≤-diff n<m = Eq.refl

<-intro-diff : {n m d : ℕ} → Positive d → n + d ≃ m → n < m
<-intro-diff pd n+d≃m =
  let n≤m = ℕ≤.≤-intro-diff n+d≃m
      d≃d[n≤m] = Eq.sym (ℕ≤P.intro-diff-id n+d≃m)
   in <-intro-≤pd n≤m (AA.subst₁ d≃d[n≤m] pd)

<-elim-diff : {n m : ℕ} (n<m : n < m) → n + <-diff n<m ≃ m
<-elim-diff n<m = ℕ≤.≤-elim-diff (<-elim-≤ n<m)

<-diff-pos : {n m : ℕ} (n<m : n < m) → Positive (<-diff n<m)
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
   in contra n≃m (<-elim-≄ n<m)
... | no d≄0 =
  ℕS.Pos-intro-≄0 d≄0
