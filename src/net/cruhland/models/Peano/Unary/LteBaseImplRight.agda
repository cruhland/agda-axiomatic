module net.cruhland.models.Peano.Unary.LteBaseImplRight where

open import Data.Nat using (ℕ; zero) renaming (suc to step)
open import Relation.Binary.PropositionalEquality using (refl)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Ordering using (_≤_; LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
import net.cruhland.models.Peano.Unary.Base as UB

module ℕ+ = Addition UB.addition

data _≤ᴿ_ (n : ℕ) : ℕ → Set where
  ≤-refl : n ≤ᴿ n
  ≤-step : ∀ {m} → n ≤ᴿ m → n ≤ᴿ step m

instance
  lessThanOrEqual : LessThanOrEqual ℕ
  lessThanOrEqual = record { _≤_ = _≤ᴿ_ }

  ≤-reflexive : Eq.Reflexive _≤_
  ≤-reflexive = Eq.reflexive ≤-refl

diff : {n m : ℕ} → n ≤ m → ℕ
diff ≤-refl = 0
diff (≤-step n≤m) = step (diff n≤m)

≤-intro-diff : {n m d : ℕ} → n + d ≃ m → n ≤ m
≤-intro-diff {n} {m} {zero} n+0≃m with Eq.trans (Eq.sym AA.identᴿ) n+0≃m
... | refl = ≤-refl
≤-intro-diff {n} {m} {step d} n+sd≃m with Eq.trans AA.fnOpCommᴿ n+sd≃m
≤-intro-diff {n} {step m} {step d} _ | s[n+d]≃sm =
  ≤-step (≤-intro-diff (AA.inject s[n+d]≃sm))

≤-elim-diff : {n m : ℕ} (n≤m : n ≤ m) → n + diff n≤m ≃ m
≤-elim-diff ≤-refl =
  AA.ident
≤-elim-diff {n} (≤-step {m} n≤m) =
  begin
    n + step (diff n≤m)
  ≃˘⟨ AA.fnOpCommᴿ ⟩
    step (n + diff n≤m)
  ≃⟨ AA.subst₁ (≤-elim-diff n≤m) ⟩
    step m
  ∎

≤-zeroᴸ : {n : ℕ} → 0 ≤ n
≤-zeroᴸ {zero} = ≤-refl
≤-zeroᴸ {step n} = ≤-step ≤-zeroᴸ

≤-widenᴿ : {n m : ℕ} → n ≤ m → n ≤ step m
≤-widenᴿ = ≤-step

instance
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
              ≃˘⟨ AA.fnOpCommᴸ {a = n} ⟩
                step (n + d)
              ≃⟨ AA.subst₁ n+d≃m ⟩
                step m
              ∎
         in ≤-intro-diff sn+d≃sm
