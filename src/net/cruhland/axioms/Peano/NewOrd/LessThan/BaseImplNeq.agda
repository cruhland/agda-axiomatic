open import net.cruhland.axioms.Eq using (_≄_)
open import net.cruhland.axioms.NewOrd using (_≤_; _<_; LessThan)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl using
  (LteBase)
open import net.cruhland.axioms.Peano.Sign using (Sign)

module net.cruhland.axioms.Peano.NewOrd.LessThan.BaseImplNeq
  (PB : PeanoBase)
  (PS : Sign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA) where

open PeanoBase PB using (ℕ)
open import net.cruhland.axioms.Peano.NewOrd.LessThan.NeqDecl PB PS PA LTEB
  as ND using (_≤≄_)

instance
  lessThan : LessThan ℕ
  lessThan = record { _<_ = _≤≄_ }

<-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n ≤≄ m
<-intro-≤≄ = ND.≤≄-intro

<-elim-≤ : {n m : ℕ} → n ≤≄ m → n ≤ m
<-elim-≤ = ND.≤≄-elim-≤

<-elim-≄ : {n m : ℕ} → n ≤≄ m → n ≄ m
<-elim-≄ = ND.≤≄-elim-≄
