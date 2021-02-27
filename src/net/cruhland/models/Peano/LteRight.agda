module net.cruhland.models.Peano.LteRight where

open import Data.Nat using (suc; zero)
-- open import Data.Nat.Properties using (≤-refl; ≤-step)
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

+d≃-from-≤ᴿ : ∀ {n m} → n ≤ᴿ m → n +d≃ m
+d≃-from-≤ᴿ ≤-refl =
  +d≃-intro AA.ident
+d≃-from-≤ᴿ {n} (≤-step {m} n≤ᴿm) =
  let +d≃-intro {d} n+d≃m = +d≃-from-≤ᴿ n≤ᴿm
      n+sd≃sm =
        begin
          n + step d
        ≃˘⟨ AA.fnOpComm ⟩
          step (n + d)
        ≃⟨ AA.subst₁ n+d≃m ⟩
          step m
        ∎
   in +d≃-intro n+sd≃sm

≤ᴿ-from-+d≃ : ∀ {n m} → n +d≃ m → n ≤ᴿ m
≤ᴿ-from-+d≃ (+d≃-intro {zero} n+0≡m) with Eq.trans (Eq.sym AA.identᴿ) n+0≡m
... | refl = ≤-refl
≤ᴿ-from-+d≃ {n} {zero} (+d≃-intro {suc d} n+sd≡0)
    with Eq.trans AA.fnOpComm n+sd≡0
... | ()
≤ᴿ-from-+d≃ {n} {suc m} (+d≃-intro {suc d} n+sd≡sm) =
  ≤-step (≤ᴿ-from-+d≃ (+d≃-intro (AA.inject (Eq.trans AA.fnOpComm n+sd≡sm))))

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
        let +d≃-intro {d} a+d≃b = +d≃-from-≤ᴿ a≤ᴿb
            sa+d≃sb =
              begin
                step a + d
              ≃˘⟨ AA.fnOpComm {a = a} ⟩
                step (a + d)
              ≃⟨ AA.subst₁ a+d≃b ⟩
                step b
              ∎
         in ≤ᴿ-from-+d≃ (+d≃-intro sa+d≃sb)

≤-base-≤ᴿ : LteBase
≤-base-≤ᴿ = record
  { ≤-intro-+d≃ = ≤ᴿ-from-+d≃
  ; ≤-elim-+d≃ = +d≃-from-≤ᴿ
  ; 0≤n = 0≤n
  ; ≤-step = ≤-step
  }
