import Agda.Builtin.FromNeg as FromNeg
open import Function using (const)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; refl; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; _*_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.models.Rationals.Negation (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers PA as ℤ using (ℤ)
import net.cruhland.models.Rationals.Addition PA as ℚ+
open import net.cruhland.models.Rationals.Base PA as ℚ using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as ℚ≃ using (≃₀-intro)
import net.cruhland.models.Rationals.Literals PA as ℚLit

instance
  dashᴸ : Op.Dashᴸ ℚ
  dashᴸ = record { -_ = -₀_ }
    where
      -₀_ : ℚ → ℚ
      -₀ (p↑ // p↓ ~ p↓≄0) = (- p↑) // p↓ ~ p↓≄0

  dash₂ : Op.Dash₂ ℚ
  dash₂ = Op.subtraction

  negative : FromNeg.Negative ℚ
  negative =
    record { Constraint = const ⊤ ; fromNeg = λ n → - Literals.fromNat n }

  neg-substitutive₁ : AA.Substitutive₁ -_ _≃_ _≃_
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
      +-invᴸ {p↑ // p↓ ~ _} = ℚ≃.q≃0 -p↑p↓+p↓p↑
        where
          -p↑p↓+p↓p↑ =
            begin
              - p↑ * p↓ + p↓ * p↑
            ≃⟨ AA.subst {a₁ = p↓ * p↑} AA.comm ⟩
              - p↑ * p↓ + p↑ * p↓
            ≃˘⟨ AA.distribᴿ ⟩
              (- p↑ + p↑) * p↓
            ≃⟨ AA.subst {f = _* p↓} AA.invᴸ ⟩
              0 * p↓
            ≃⟨ AA.absorbᴸ ⟩
              0
            ∎

  +-inverseᴿ : AA.Inverseᴿ {A = ℚ} _+_ -_ 0
  +-inverseᴿ = AA.inverseᴿ
