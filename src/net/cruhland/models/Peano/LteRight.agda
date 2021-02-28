module net.cruhland.models.Peano.LteRight where

open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (refl)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.NewOrd using (LessThanOrEqual)
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.Base as LteBase
open import net.cruhland.models.Function using (_⟨→⟩_; id)
import net.cruhland.models.Peano.Unary as U

open module LB = LteBase U.base U.sign U.addition using
  (_+d≃_; +d≃-intro; LteBase)
module ℕ+ = Addition U.addition
open PeanoBase U.base using (ℕ; step)

data _≤ᴿ_ (n : ℕ) : ℕ → Set where
  ≤-refl : n ≤ᴿ n
  ≤-step : ∀ {m} → n ≤ᴿ m → n ≤ᴿ step m

diff : ∀ {n m} → n ≤ᴿ m → ℕ
diff ≤-refl = 0
diff (≤-step n≤ᴿm) = step (diff n≤ᴿm)

n≤ᴿm-from-n+d≃m : ∀ {n m d} → n + d ≃ m → n ≤ᴿ m
n≤ᴿm-from-n+d≃m {n} {m} {zero} n+0≡m with Eq.trans (Eq.sym AA.identᴿ) n+0≡m
... | refl = ≤-refl
n≤ᴿm-from-n+d≃m {n} {zero} {suc d} n+sd≡0 with Eq.trans AA.fnOpComm n+sd≡0
... | ()
n≤ᴿm-from-n+d≃m {n} {suc m} {suc d} n+sd≡sm =
  ≤-step (n≤ᴿm-from-n+d≃m (AA.inject (Eq.trans AA.fnOpComm n+sd≡sm)))

n+d≃m-from-n≤ᴿm : ∀ {n m} (n≤ᴿm : n ≤ᴿ m) → n + diff n≤ᴿm ≃ m
n+d≃m-from-n≤ᴿm ≤-refl = AA.ident
n+d≃m-from-n≤ᴿm {n} (≤-step {m} n≤ᴿm) =
  begin
    n + step (diff n≤ᴿm)
  ≃˘⟨ AA.fnOpComm ⟩
    step (n + diff n≤ᴿm)
  ≃⟨ AA.subst₁ (n+d≃m-from-n≤ᴿm n≤ᴿm) ⟩
    step m
  ∎

0≤n : ∀ {n} → 0 ≤ᴿ n
0≤n {zero} = ≤-refl
0≤n {suc n} = ≤-step 0≤n

instance
  lessThanOrEqual-≤ᴸ : LessThanOrEqual ℕ
  lessThanOrEqual-≤ᴸ = record { _≤_ = _≤ᴿ_ }

  substitutive-≤ᴿ-≃ᴸ : AA.Substitutive₂ AA.handᴸ _≤ᴿ_ _≃_ _⟨→⟩_
  substitutive-≤ᴿ-≃ᴸ = AA.substitutive₂ λ { refl → id }

  substitutive-≤ᴿ-≃ᴿ : AA.Substitutive₂ AA.handᴿ _≤ᴿ_ _≃_ _⟨→⟩_
  substitutive-≤ᴿ-≃ᴿ = AA.substitutive₂ λ { refl → id }

  substitutive-≤ᴿ-≃ : AA.Substitutive₂² _≤ᴿ_ _≃_ _⟨→⟩_
  substitutive-≤ᴿ-≃ = AA.substitutive₂²

  reflexive-≤ᴿ : Eq.Reflexive _≤ᴿ_
  reflexive-≤ᴿ = Eq.reflexive ≤-refl

  substitutive-step-≤ᴿ : AA.Substitutive₁ step _≤ᴿ_ _≤ᴿ_
  substitutive-step-≤ᴿ = AA.substitutive₁ subst-step-≤ᴿ
    where
      subst-step-≤ᴿ : ∀ {a b} → a ≤ᴿ b → step a ≤ᴿ step b
      subst-step-≤ᴿ {a} {b} a≤ᴿb =
        let sa+d≃sb =
              begin
                step a + diff a≤ᴿb
              ≃˘⟨ AA.fnOpComm {a = a} ⟩
                step (a + diff a≤ᴿb)
              ≃⟨ AA.subst₁ (n+d≃m-from-n≤ᴿm a≤ᴿb) ⟩
                step b
              ∎
         in n≤ᴿm-from-n+d≃m sa+d≃sb

≤-base-≤ᴿ : LteBase
≤-base-≤ᴿ = record
  { diff = diff
  ; ≤-intro-diff = n≤ᴿm-from-n+d≃m
  ; ≤-elim-diff = n+d≃m-from-n≤ᴿm
  ; 0≤n = 0≤n
  ; ≤-step = ≤-step
  }
