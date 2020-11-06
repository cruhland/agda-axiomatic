import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.Addition (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open ℤ using (ℤ)
open import net.cruhland.models.Rationals.Base PA using (ℚ)
open import net.cruhland.models.Rationals.Equality PA as Equality using
  (≃₀-intro)

instance
  plus : Op.Plus ℚ
  plus = record { _+_ = _+₀_ }
    where
      _+₀_ : ℚ → ℚ → ℚ
      record { n = p↑ ; d = p↓ ; d≄0 = p↓≄0 } +₀
        record { n = q↑ ; d = q↓ ; d≄0 = q↓≄0 } =
          record
            { n = p↑ * q↓ + p↓ * q↑
            ; d = p↓ * q↓
            ; d≄0 = AA.nonzero-prod p↓≄0 q↓≄0
            }

  +-commutative : AA.Commutative _+_
  +-commutative = record { comm = +-comm }
    where
      +-comm : {a b : ℚ} → a + b ≃ b + a
      +-comm {record { n = a↑ ; d = a↓ }} {record { n = b↑ ; d = b↓ }} =
          ≃₀-intro [a↑b↓+a↓b↑][b↓a↓]≃[b↑a↓+b↓a↑][a↓b↓]
        where
          [a↑b↓+a↓b↑][b↓a↓]≃[b↑a↓+b↓a↑][a↓b↓] =
            begin
              (a↑ * b↓ + a↓ * b↑) * (b↓ * a↓)
            ≃⟨ AA.substᴸ (AA.substᴸ AA.comm) ⟩
              (b↓ * a↑ + a↓ * b↑) * (b↓ * a↓)
            ≃⟨ AA.substᴸ (AA.substᴿ AA.comm) ⟩
              (b↓ * a↑ + b↑ * a↓) * (b↓ * a↓)
            ≃⟨ AA.substᴸ AA.comm ⟩
              (b↑ * a↓ + b↓ * a↑) * (b↓ * a↓)
            ≃⟨ AA.substᴿ AA.comm ⟩
              (b↑ * a↓ + b↓ * a↑) * (a↓ * b↓)
            ∎

  +-substitutiveᴸ : AA.Substitutiveᴸ _+_
  +-substitutiveᴸ = record { substᴸ = +-substᴸ }
    where
      +-substᴸ : {a₁ a₂ b : ℚ} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
      +-substᴸ
        {record { n = a₁↑ ; d = a₁↓ }}
        {record { n = a₂↑ ; d = a₂↓ }}
        {record { n = b↑ ; d = b↓ }}
        (≃₀-intro a₁↑a₂↓≃a₂↑a₁↓) =
          ≃₀-intro [a₁↑b↓+a₁↓b↑][a₂↓b↓]≃[a₂↑b↓+a₂↓b↑][a₁↓b↓]
        where
          prepare :
            {u v w x y z : ℤ} →
              (w * x + u * v) * (y * z) ≃ w * y * (x * z) + v * u * (y * z)
          prepare {u} {v} {w} {x} {y} {z} =
            begin
              (w * x + u * v) * (y * z)
            ≃⟨ AA.distribᴿ ⟩
              w * x * (y * z) + u * v * (y * z)
            ≃⟨ AA.substᴸ AA.transpose ⟩
              w * y * (x * z) + u * v * (y * z)
            ≃⟨ AA.substᴿ (AA.substᴸ AA.comm) ⟩
              w * y * (x * z) + v * u * (y * z)
            ∎

          [a₁↑b↓+a₁↓b↑][a₂↓b↓]≃[a₂↑b↓+a₂↓b↑][a₁↓b↓] =
            begin
              (a₁↑ * b↓ + a₁↓ * b↑) * (a₂↓ * b↓)
            ≃⟨ prepare ⟩
              a₁↑ * a₂↓ * (b↓ * b↓) + b↑ * a₁↓ * (a₂↓ * b↓)
            ≃⟨ AA.substᴸ (AA.substᴸ a₁↑a₂↓≃a₂↑a₁↓) ⟩
              a₂↑ * a₁↓ * (b↓ * b↓) + b↑ * a₁↓ * (a₂↓ * b↓)
            ≃⟨ AA.substᴿ AA.transpose ⟩
               a₂↑ * a₁↓ * (b↓ * b↓) + b↑ * a₂↓ * (a₁↓ * b↓)
            ≃˘⟨ prepare ⟩
              (a₂↑ * b↓ + a₂↓ * b↑) * (a₁↓ * b↓)
            ∎

  +-substitutiveᴿ : AA.Substitutiveᴿ {A = ℚ} _+_
  +-substitutiveᴿ = AA.substitutiveᴿ

  +-substitutive₂ : AA.Substitutive₂ {A = ℚ} _+_
  +-substitutive₂ = AA.substitutive₂
