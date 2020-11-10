import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.Multiplication (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers PA as ℤ using (ℤ)
import net.cruhland.models.Rationals.Addition PA as Addition
open import net.cruhland.models.Rationals.Base PA as Base using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as Equality using
  (≃₀-intro)

instance
  star : Op.Star ℚ
  star = record { _*_ = _*₀_ }
    where
      _*₀_ : ℚ → ℚ → ℚ
      (p↑ // p↓ ~ p↓≄0) *₀ (q↑ // q↓ ~ q↓≄0) =
        (p↑ * q↑) // p↓ * q↓ ~ AA.nonzero-prod p↓≄0 q↓≄0

  *-commutative : AA.Commutative _*_
  *-commutative = record { comm = *-comm }
    where
      *-comm : {a b : ℚ} → a * b ≃ b * a
      *-comm {a↑ // a↓ ~ _} {b↑ // b↓ ~ _} =
          ≃₀-intro [a↑b↑][b↓a↓]≃[b↑a↑][a↓b↓]
        where
          [a↑b↑][b↓a↓]≃[b↑a↑][a↓b↓] =
            begin
              a↑ * b↑ * (b↓ * a↓)
            ≃⟨ AA.substᴸ AA.comm ⟩
              b↑ * a↑ * (b↓ * a↓)
            ≃⟨ AA.substᴿ AA.comm ⟩
              b↑ * a↑ * (a↓ * b↓)
            ∎

  *-substitutiveᴸ : AA.Substitutiveᴸ _*_
  *-substitutiveᴸ = record { substᴸ = *-substᴸ }
    where
      *-substᴸ : {a₁ a₂ b : ℚ} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
      *-substᴸ
        {a₁↑ // a₁↓ ~ _} {a₂↑ // a₂↓ ~ _} {b↑ // b↓ ~ _}
        (≃₀-intro a₁↑a₂↓≃a₂↑a₁↓) =
          ≃₀-intro [a₁↑b↑][a₂↓b↓]≃[a₂↑b↑][a₁↓b↓]
        where
          [a₁↑b↑][a₂↓b↓]≃[a₂↑b↑][a₁↓b↓] =
            begin
              a₁↑ * b↑ * (a₂↓ * b↓)
            ≃⟨ AA.transpose ⟩
              a₁↑ * a₂↓ * (b↑ * b↓)
            ≃⟨ AA.substᴸ a₁↑a₂↓≃a₂↑a₁↓ ⟩
              a₂↑ * a₁↓ * (b↑ * b↓)
            ≃˘⟨ AA.transpose ⟩
              a₂↑ * b↑ * (a₁↓ * b↓)
            ∎

  *-substitutiveᴿ : AA.Substitutiveᴿ {A = ℚ} _*_
  *-substitutiveᴿ = AA.substitutiveᴿ

  *-substitutive₂ : AA.Substitutive₂ {A = ℚ} _*_
  *-substitutive₂ = AA.substitutive₂

  *-compatible-ℤ : AA.Compatible₂ {A = ℤ} (_as ℚ) _*_ _*_
  *-compatible-ℤ = record { compat₂ = ≃₀-intro (AA.substᴿ AA.identᴿ) }
