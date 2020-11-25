import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; sym; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Literals

module net.cruhland.models.Rationals.Addition (PA : PeanoArithmetic) where

import net.cruhland.models.Integers PA as ℤ
open ℤ using (ℤ)
open import net.cruhland.models.Rationals.Base PA as ℚ using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as ℚ≃ using (≃₀-intro)
import net.cruhland.models.Rationals.Literals PA as ℚLit

instance
  plus : Op.Plus ℚ
  plus = record { _+_ = _+₀_ }
    where
      _+₀_ : ℚ → ℚ → ℚ
      (p↑ // p↓ ~ p↓≄0) +₀ (q↑ // q↓ ~ q↓≄0) =
        (p↑ * q↓ + p↓ * q↑) // p↓ * q↓ ~ AA.nonzero-prod p↓≄0 q↓≄0

  +-commutative : AA.Commutative _+_
  +-commutative = record { comm = +-comm }
    where
      +-comm : {a b : ℚ} → a + b ≃ b + a
      +-comm {a↑ // a↓ ~ _} {b↑ // b↓ ~ _} =
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

  +-substitutiveᴸ : AA.Substitutiveᴸ _≃_ _≃_ _+_
  +-substitutiveᴸ = record { substᴸ = +-substᴸ }
    where
      +-substᴸ : {a₁ a₂ b : ℚ} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
      +-substᴸ
        {a₁↑ // a₁↓ ~ _} {a₂↑ // a₂↓ ~ _} {b↑ // b↓ ~ _}
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

  +-compatible-ℤ : AA.Compatible₂ {A = ℤ} (_as ℚ) _+_ _+_
  +-compatible-ℤ = record { compat₂ = +-compat-ℤ }
    where
      +-compat-ℤ : {a b : ℤ} → (a + b as ℚ) ≃ (a as ℚ) + (b as ℚ)
      +-compat-ℤ {a} {b} = ≃₀-intro [a+b][1*1]≃[a1+1b]1
        where
          [a+b][1*1]≃[a1+1b]1 =
            begin
              (a + b) * (1 * 1)
            ≃⟨ AA.substᴿ AA.identᴿ ⟩
              (a + b) * 1
            ≃˘⟨ AA.substᴸ (AA.substᴸ AA.identᴿ) ⟩
              (a * 1 + b) * 1
            ≃˘⟨ AA.substᴸ (AA.substᴿ AA.identᴸ) ⟩
              (a * 1 + 1 * b) * 1
            ∎

  +-associative : AA.Associative _+_
  +-associative = record { assoc = +-assoc }
    where
      +-assoc : {p q r : ℚ} → (p + q) + r ≃ p + (q + r)
      +-assoc {p↑ // p↓ ~ _} {q↑ // q↓ ~ _} {r↑ // r↓ ~ _} =
          ≃₀-intro (AA.[a≃b][c≃d] ≃-numer ≃-denom)
        where
          ≃-numer =
            begin
              (p↑ * q↓ + p↓ * q↑) * r↓ + (p↓ * q↓) * r↑
            ≃⟨ AA.substᴸ AA.distribᴿ ⟩
              ((p↑ * q↓) * r↓ + (p↓ * q↑) * r↓) + (p↓ * q↓) * r↑
            ≃⟨ AA.substᴸ (AA.substᴸ AA.assoc) ⟩
              (p↑ * (q↓ * r↓) + (p↓ * q↑) * r↓) + (p↓ * q↓) * r↑
            ≃⟨ AA.substᴸ (AA.substᴿ AA.assoc) ⟩
              (p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓)) + (p↓ * q↓) * r↑
            ≃⟨ AA.substᴿ AA.assoc ⟩
              (p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓)) + p↓ * (q↓ * r↑)
            ≃⟨ AA.assoc ⟩
              p↑ * (q↓ * r↓) + (p↓ * (q↑ * r↓) + p↓ * (q↓ * r↑))
            ≃˘⟨ AA.substᴿ AA.distribᴸ ⟩
              p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓ + q↓ * r↑)
            ∎

          ≃-denom = sym AA.assoc

  +-identityᴸ : AA.Identityᴸ _+_ 0
  +-identityᴸ = record { identᴸ = +-identᴸ }
    where
      +-identᴸ : {p : ℚ} → 0 + p ≃ p
      +-identᴸ {p↑ // p↓ ~ _} = ≃₀-intro (AA.[a≃b][c≃d] ≃-numer ≃-denom)
        where
          ≃-numer =
            begin
              0 * p↓ + 1 * p↑
            ≃⟨ AA.substᴸ AA.absorbᴸ ⟩
              0 + 1 * p↑
            ≃⟨ AA.identᴸ ⟩
              1 * p↑
            ≃⟨ AA.identᴸ ⟩
              p↑
            ∎

          ≃-denom = sym AA.identᴸ

  +-identityᴿ : AA.Identityᴿ {A = ℚ} _+_ 0
  +-identityᴿ = AA.identityᴿ
