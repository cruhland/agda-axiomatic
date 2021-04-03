import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (_≤_; _<_; LessThan)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.BaseDecl
  using (LteBase)
open import net.cruhland.axioms.Peano.NewOrd.LessThanOrEqual.PropertiesDecl
  using (LteProperties)
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
open import net.cruhland.axioms.Sign as Sign using (Positive)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contra; no; yes)

module net.cruhland.axioms.Peano.NewOrd.LessThan.BaseImplPosDiff
  (PB : PeanoBase)
  (PS : ℕSign PB)
  (PA : Addition PB PS)
  (LTEB : LteBase PB PS PA)
  (LTEP : LteProperties PB PS PA LTEB)
  where

private module ℕ+ = Addition PA
open PeanoBase PB using (ℕ)
import net.cruhland.axioms.Peano.Inspect PB as ℕI
import net.cruhland.axioms.Peano.Literals PB as ℕL
private module ℕ≤ = LteBase LTEB
private module ℕ≤P = LteProperties LTEP
private module ℕS = ℕSign PS
import net.cruhland.axioms.Peano.NewOrd.LessThan.PosDiffDecl PB PS PA LTEB as PD

instance
  lessThan : LessThan ℕ
  lessThan = record { _<_ = PD._≤⁺_ }

<-intro-≤pd : {n m : ℕ} (n≤m : n ≤ m) → Positive (ℕ≤.≤-diff n≤m) → n < m
<-intro-≤pd = PD.≤⁺-intro

<-intro-≤≄ : {n m : ℕ} → n ≤ m → n ≄ m → n < m
<-intro-≤≄ n≤m n≄m with ℕ≤.≤-diff n≤m ≃? 0
... | yes d≃0 = contra (ℕ≤P.zero-diff n≤m d≃0) n≄m
... | no d≄0 = <-intro-≤pd n≤m (ℕS.Pos-intro-≄0 d≄0)

<-elim-≤ : {n m : ℕ} → n < m → n ≤ m
<-elim-≤ = PD.≤⁺-elim-n≤m

<-diff : {n m : ℕ} → n < m → ℕ
<-diff n<m = ℕ≤.≤-diff (<-elim-≤ n<m)

<-diff-from-≤-diff :
  {n m : ℕ} (n<m : n < m) → <-diff n<m ≃ ℕ≤.≤-diff (<-elim-≤ n<m)
<-diff-from-≤-diff n<m = Eq.refl

<-diff-pos : {n m : ℕ} (n<m : n < m) → Positive (<-diff n<m)
<-diff-pos = PD.≤⁺-elim-d⁺

<-intro-diff : {n m d : ℕ} → Positive d → n + d ≃ m → n < m
<-intro-diff pos[d] n+d≃m =
  let n≤m = ℕ≤.≤-intro-diff n+d≃m
      pos[d[n≤m]] = AA.subst₁ (Eq.sym (ℕ≤P.intro-diff-id n+d≃m)) pos[d]
   in PD.≤⁺-intro n≤m pos[d[n≤m]]

<-elim-diff : {n m : ℕ} (n<m : n < m) → n + <-diff n<m ≃ m
<-elim-diff n<m = ℕ≤.≤-elim-diff (<-elim-≤ n<m)

<-elim-≄ : {n m : ℕ} → n < m → n ≄ m
<-elim-≄ {n} {m} n<m n≃m =
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
   in contra d≃0 d≄0
