-- Needed for positive integer literals (typeclass)
import Agda.Builtin.FromNat
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; refl; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; _*_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for positive integer literals (instance for ⊤)
import net.cruhland.models.Logic

module net.cruhland.models.Rationals.Negation (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers PA as ℤ using (ℤ)
import net.cruhland.models.Rationals.Addition PA as Addition
open import net.cruhland.models.Rationals.Base PA as Base using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as Equality using
  (≃₀-intro)

instance
  dashᴸ : Op.Dashᴸ ℚ
  dashᴸ = record { -_ = -₀_ }
    where
      -₀_ : ℚ → ℚ
      -₀ (p↑ // p↓ ~ p↓≄0) = (- p↑) // p↓ ~ p↓≄0

  dash₂ : Op.Dash₂ ℚ
  dash₂ = Op.subtraction

  neg-substitutive₁ : AA.Substitutive₁ -_
  neg-substitutive₁ = record { subst = neg-subst }
    where
      neg-subst : {a₁ a₂ : ℚ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
      neg-subst {a₁↑ // a₁↓ ~ _} {a₂↑ // a₂↓ ~ _} (≃₀-intro a₁↑a₂↓≃a₂↑a₁↓) =
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

  +-inverseᴸ : AA.Inverseᴸ _+_ -_ 0
  +-inverseᴸ = record { invᴸ = +-invᴸ }
    where
      +-invᴸ : {p : ℚ} → (- p) + p ≃ 0
      +-invᴸ {p↑ // p↓ ~ _} = Equality.q≃0 -p↑p↓+p↓p↑
        where
          -p↑p↓+p↓p↑ =
            begin
              - p↑ * p↓ + p↓ * p↑
            ≃⟨ AA.substᴿ AA.comm ⟩
              - p↑ * p↓ + p↑ * p↓
            ≃˘⟨ AA.distribᴿ ⟩
              (- p↑ + p↑) * p↓
            ≃⟨ AA.substᴸ AA.invᴸ ⟩
              0 * p↓
            ≃⟨ AA.absorbᴸ ⟩
              0
            ∎

  +-inverseᴿ : AA.Inverseᴿ {A = ℚ} _+_ -_ 0
  +-inverseᴿ = AA.inverseᴿ
