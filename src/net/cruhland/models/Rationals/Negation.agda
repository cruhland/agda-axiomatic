import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; refl; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_*_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.Negation (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers PA as ℤ using (ℤ)
open import net.cruhland.models.Rationals.Base PA as Base using (ℚ)
open import net.cruhland.models.Rationals.Equality PA as Equality using
  (≃₀-intro)

instance
  dashᴸ : Op.Dashᴸ ℚ
  dashᴸ = record { -_ = -₀_ }
    where
      -₀_ : ℚ → ℚ
      -₀ record { n = p↑ ; d = p↓ ; d≄0 = p↓≄0 } =
        record { n = - p↑ ; d = p↓ ; d≄0 = p↓≄0 }

  neg-substitutive₁ : AA.Substitutive₁ -_
  neg-substitutive₁ = record { subst = neg-subst }
    where
      neg-subst : {a₁ a₂ : ℚ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
      neg-subst
        {record { n = a₁↑ ; d = a₁↓ }}
        {record { n = a₂↑ ; d = a₂↓ }}
        (≃₀-intro a₁↑a₂↓≃a₂↑a₁↓) =
          ≃₀-intro [-a₁↑]a₂↓≃[-a₂↑]a₁↓
        where
          [-a₁↑]a₂↓≃[-a₂↑]a₁↓ =
            begin
              - a₁↑ * a₂↓
            ≃⟨ AA.commᴸ ⟩
              - (a₁↑ * a₂↓)
            ≃⟨ AA.subst a₁↑a₂↓≃a₂↑a₁↓ ⟩
              - (a₂↑ * a₁↓)
            ≃˘⟨ AA.commᴸ ⟩
              - a₂↑ * a₁↓
            ∎

  neg-compatible-ℤ : AA.Compatible₁ {A = ℤ} (_as ℚ) -_ -_
  neg-compatible-ℤ = record { compat₁ = ≃₀-intro refl }
