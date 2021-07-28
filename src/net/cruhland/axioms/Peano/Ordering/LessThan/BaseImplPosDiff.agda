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
open import net.cruhland.axioms.Sign as Sign using (Positive)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_; no; yes)

module net.cruhland.axioms.Peano.Ordering.LessThan.BaseImplPosDiff
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
import net.cruhland.axioms.Peano.Ordering.LessThan.PosDiffDecl PB PS PA LTEB
  as PD

instance
  lessThan : Ord.LessThan ℕ
  lessThan = Ord.lessThan PD._≤⁺_

<-intro-≤pd : {n m : ℕ} (n≤m : n ≤ m) → Positive (ℕ.≤-diff n≤m) → n < m
<-intro-≤pd = PD.≤⁺-intro

<-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n < m
<-intro-≤≄ n≤m n≄m with ℕ.≤-diff n≤m ≃? 0
... | yes d≃0 =
  let n≃m = ℕ.zero-diff n≤m d≃0
   in n≃m ↯ n≄m
... | no d≄0 =
  let pos[d] = ℕ.Pos-intro-≄0 d≄0
   in <-intro-≤pd n≤m pos[d]

<-elim-≤ : {n m : ℕ} → n < m → n ≤ m
<-elim-≤ = PD.≤⁺-elim-n≤m

<-diff : {n m : ℕ} → n < m → ℕ
<-diff n<m = ℕ.≤-diff (<-elim-≤ n<m)

<-diff-from-≤-diff :
  {n m : ℕ} (n<m : n < m) → <-diff n<m ≃ ℕ.≤-diff (<-elim-≤ n<m)
<-diff-from-≤-diff n<m = Eq.refl

<-diff-pos : {n m : ℕ} (n<m : n < m) → Positive (<-diff n<m)
<-diff-pos = PD.≤⁺-elim-d⁺

<-intro-diff : {n m d : ℕ} → Positive d → n + d ≃ m → n < m
<-intro-diff pos[d] n+d≃m =
  let n≤m = ℕ.≤-intro-diff n+d≃m
      pos[d[n≤m]] = AA.subst₁ (Eq.sym (ℕ.intro-diff-id n+d≃m)) pos[d]
   in PD.≤⁺-intro n≤m pos[d[n≤m]]

<-elim-diff : {n m : ℕ} (n<m : n < m) → n + <-diff n<m ≃ m
<-elim-diff n<m = ℕ.≤-elim-diff (<-elim-≤ n<m)

<-elim-≄ : {n m : ℕ} → n < m → n ≄ m
<-elim-≄ {n} {m} n<m = Eq.≄-intro λ n≃m →
  let n+d≃n+0 =
        begin
          n + <-diff n<m
        ≃⟨ <-elim-diff n<m ⟩
          m
        ≃˘⟨ n≃m ⟩
          n
        ≃˘⟨ AA.ident ⟩
          n + 0
        ∎
      d≃0 = AA.cancel n+d≃n+0
      d≄0 = Sign.pos≄0 (<-diff-pos n<m)
   in d≃0 ↯ d≄0
