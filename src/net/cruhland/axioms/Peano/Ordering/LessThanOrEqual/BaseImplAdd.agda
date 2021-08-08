import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Ordering using (_≤_; LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.AddDecl as AddDecl
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.BaseImplAdd
  (PB : PeanoBase) (PS : Sign PB) (PA : Addition PB PS) where

private module AD = AddDecl PB PS PA
private module ℕ+ = Addition PA
open PeanoBase PB using (ℕ; step)
import net.cruhland.axioms.Peano.Literals PB as ℕL

instance
  lessThanOrEqual : LessThanOrEqual ℕ
  lessThanOrEqual = record { _≤_ = AD._+d≃_ }

diff : {n m : ℕ} → n ≤ m → ℕ
diff = AD.diff

≤-intro-diff : {n m d : ℕ} → n + d ≃ m → n ≤ m
≤-intro-diff = AD.+d≃-intro

≤-elim-diff : {n m : ℕ} (n≤m : n ≤ m) → n + diff n≤m ≃ m
≤-elim-diff = AD.+d≃-elim

instance
  ≤-reflexive : Eq.Reflexive _≤_
  ≤-reflexive = Eq.reflexive (≤-intro-diff AA.ident)

  ≤-substitutive-step : AA.Substitutive₁ step _≤_ _≤_
  ≤-substitutive-step = AA.substitutive₁ ≤-subst-step
    where
      ≤-subst-step : {n m : ℕ} → n ≤ m → step n ≤ step m
      ≤-subst-step {n} {m} n≤m =
        let d = diff n≤m
            n+d≃m = ≤-elim-diff n≤m
            sn+d≃sm =
              begin
                step n + d
              ≃˘⟨ AA.fnOpCommᴸ ⟩
                step (n + d)
              ≃⟨ AA.subst₁ n+d≃m ⟩
                step m
              ∎
         in ≤-intro-diff sn+d≃sm

≤-zeroᴸ : {n : ℕ} → 0 ≤ n
≤-zeroᴸ {n} = ≤-intro-diff AA.ident

≤-widenᴿ : {n m : ℕ} → n ≤ m → n ≤ step m
≤-widenᴿ {n} {m} n≤m = ≤-intro-diff n+sd≃sm
  where
    n+sd≃sm =
      begin
        n + step (diff n≤m)
      ≃˘⟨ AA.fnOpCommᴿ ⟩
        step (n + diff n≤m)
      ≃⟨ AA.subst₁ (≤-elim-diff n≤m) ⟩
        step m
      ∎
