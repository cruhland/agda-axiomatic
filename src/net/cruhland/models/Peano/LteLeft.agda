module net.cruhland.models.Peano.LteLeft where

open import Data.Nat using (suc; s≤s; zero; z≤n) renaming (_≤_ to _≤ᴸ_)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Relation.Binary.PropositionalEquality using (refl)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.NewOrd using (LessThanOrEqual)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Ordering.LessThanOrEqual.Base as LteBase
open import net.cruhland.models.Function using (_⟨→⟩_; id)
import net.cruhland.models.Peano.Unary as U

open module LB = LteBase U.base U.sign U.addition using
  (_+d≃_; +d≃-intro; 0+d≃n; LteBase)
open PeanoBase U.base using (ℕ; step)

+d≃-from-≤ᴸ : ∀ {n m} → n ≤ᴸ m → n +d≃ m
+d≃-from-≤ᴸ z≤n = 0+d≃n
+d≃-from-≤ᴸ (s≤s n≤ᴸm) = AA.subst₁ (+d≃-from-≤ᴸ n≤ᴸm)

≤ᴸ-from-+d≃ : ∀ {n m} → n +d≃ m → n ≤ᴸ m
≤ᴸ-from-+d≃ {zero} _ =
  z≤n
≤ᴸ-from-+d≃ {suc n} {suc m} (+d≃-intro refl) =
  s≤s (≤ᴸ-from-+d≃ (+d≃-intro refl))

instance
  lessThanOrEqual-≤ᴸ : LessThanOrEqual ℕ
  lessThanOrEqual-≤ᴸ = record { _≤_ = _≤ᴸ_ }

  substitutive-≤ᴸ-≃ᴸ : AA.Substitutive₂ AA.handᴸ _≤ᴸ_ _≃_ _⟨→⟩_
  substitutive-≤ᴸ-≃ᴸ = AA.substitutive₂ λ { refl → id }

  substitutive-≤ᴸ-≃ᴿ : AA.Substitutive₂ AA.handᴿ _≤ᴸ_ _≃_ _⟨→⟩_
  substitutive-≤ᴸ-≃ᴿ = AA.substitutive₂ λ { refl → id }

  substitutive-≤ᴸ-≃ : AA.Substitutive₂² _≤ᴸ_ _≃_ _⟨→⟩_
  substitutive-≤ᴸ-≃ = AA.substitutive₂²

  reflexive-≤ᴸ : Eq.Reflexive _≤ᴸ_
  reflexive-≤ᴸ = Eq.reflexive ≤-refl

  substitutive-step-≤ᴸ : AA.Substitutive₁ step _≤ᴸ_ _≤ᴸ_
  substitutive-step-≤ᴸ = AA.substitutive₁ s≤s

≤-base-≤ᴸ : LteBase
≤-base-≤ᴸ = record
  { ≤-intro-+d≃ = ≤ᴸ-from-+d≃
  ; ≤-elim-+d≃ = +d≃-from-≤ᴸ
  ; 0≤n = z≤n
  ; ≤-step = ≤-step
  }
