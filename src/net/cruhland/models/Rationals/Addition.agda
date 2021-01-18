import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; sym; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

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
            ≃⟨ AA.subst {f = _* (b↓ * a↓)} (AA.subst {f = _+ a↓ * b↑} AA.comm) ⟩
              (b↓ * a↑ + a↓ * b↑) * (b↓ * a↓)
            ≃⟨ AA.subst {f = _* (b↓ * a↓)} (AA.subst {a₁ = a↓ * b↑} AA.comm) ⟩
              (b↓ * a↑ + b↑ * a↓) * (b↓ * a↓)
            ≃⟨ AA.subst {f = _* (b↓ * a↓)} AA.comm ⟩
              (b↑ * a↓ + b↓ * a↑) * (b↓ * a↓)
            ≃⟨ AA.subst {a₁ = b↓ * a↓} AA.comm ⟩
              (b↑ * a↓ + b↓ * a↑) * (a↓ * b↓)
            ∎

  +-substitutiveᴸ : AA.Substitutiveᴸ _+_
  +-substitutiveᴸ {b@(b↑ // b↓ ~ _)} = AA.substitutive₁ +-substᴸ
    where
      +-substᴸ : {a₁ a₂ : ℚ} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
      +-substᴸ
        {a₁↑ // a₁↓ ~ _} {a₂↑ // a₂↓ ~ _} (≃₀-intro a₁↑a₂↓≃a₂↑a₁↓) =
          ≃₀-intro [a₁↑b↓+a₁↓b↑][a₂↓b↓]≃[a₂↑b↓+a₂↓b↑][a₁↓b↓]
        where
          prepare :
            {u v w x y z : ℤ} →
              (w * x + u * v) * (y * z) ≃ w * y * (x * z) + v * u * (y * z)
          prepare {u} {v} {w} {x} {y} {z} =
            begin
              (w * x + u * v) * (y * z)
            ≃⟨ AA.distrib ⟩
              w * x * (y * z) + u * v * (y * z)
            ≃⟨ AA.subst {f = _+ u * v * (y * z)} AA.transpose ⟩
              w * y * (x * z) + u * v * (y * z)
            ≃⟨ AA.subst {f = w * y * (x * z) +_}
                 (AA.subst {f = _* (y * z)} AA.comm) ⟩
              w * y * (x * z) + v * u * (y * z)
            ∎

          [a₁↑b↓+a₁↓b↑][a₂↓b↓]≃[a₂↑b↓+a₂↓b↑][a₁↓b↓] =
            begin
              (a₁↑ * b↓ + a₁↓ * b↑) * (a₂↓ * b↓)
            ≃⟨ prepare ⟩
              a₁↑ * a₂↓ * (b↓ * b↓) + b↑ * a₁↓ * (a₂↓ * b↓)
            ≃⟨ AA.subst (AA.subst {f = _* (b↓ * b↓)} a₁↑a₂↓≃a₂↑a₁↓) ⟩
              a₂↑ * a₁↓ * (b↓ * b↓) + b↑ * a₁↓ * (a₂↓ * b↓)
            ≃⟨ AA.subst {f = a₂↑ * a₁↓ * (b↓ * b↓) +_} AA.transpose ⟩
               a₂↑ * a₁↓ * (b↓ * b↓) + b↑ * a₂↓ * (a₁↓ * b↓)
            ≃˘⟨ prepare ⟩
              (a₂↑ * b↓ + a₂↓ * b↑) * (a₁↓ * b↓)
            ∎

  +-substitutiveᴿ : AA.Substitutiveᴿ _+_
  +-substitutiveᴿ = AA.substitutiveᴿ {A = ℚ}

  +-substitutive₂ : AA.Substitutive₂ _+_
  +-substitutive₂ = AA.substitutive₂ {A = ℚ}

  +-compatible-ℤ : AA.Compatible₂ (_as ℚ) _+_
  +-compatible-ℤ = AA.compatible₂ {A = ℤ} _+_ +-compat-ℤ
    where
      +-compat-ℤ : {a b : ℤ} → (a + b as ℚ) ≃ (a as ℚ) + (b as ℚ)
      +-compat-ℤ {a} {b} = ≃₀-intro [a+b][1*1]≃[a1+1b]1
        where
          [a+b][1*1]≃[a1+1b]1 =
            begin
              (a + b) * (1 * 1)
            ≃⟨ AA.subst {f = (a + b) *_} AA.identᴿ ⟩
              (a + b) * 1
            ≃˘⟨ AA.subst {A = ℤ} {f = _* 1} (AA.subst {f = _+ b} AA.ident) ⟩
              (a * 1 + b) * 1
            ≃˘⟨ AA.subst {A = ℤ} {f = _* 1}
                  (AA.subst {f = a * 1 +_} AA.ident) ⟩
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
            ≃⟨ AA.subst AA.distribᴿ ⟩
              ((p↑ * q↓) * r↓ + (p↓ * q↑) * r↓) + (p↓ * q↓) * r↑
            ≃⟨ AA.subst {f = _+ (p↓ * q↓) * r↑}
                 (AA.subst {f = _+ (p↓ * q↑) * r↓} AA.assoc) ⟩
              (p↑ * (q↓ * r↓) + (p↓ * q↑) * r↓) + (p↓ * q↓) * r↑
            ≃⟨ AA.subst {f = _+ (p↓ * q↓) * r↑}
                 (AA.subst {f = p↑ * (q↓ * r↓) +_} AA.assoc) ⟩
              (p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓)) + (p↓ * q↓) * r↑
            ≃⟨ AA.subst {a₁ = (p↓ * q↓) * r↑} AA.assoc ⟩
              (p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓)) + p↓ * (q↓ * r↑)
            ≃⟨ AA.assoc ⟩
              p↑ * (q↓ * r↓) + (p↓ * (q↑ * r↓) + p↓ * (q↓ * r↑))
            ≃˘⟨ AA.subst AA.distribᴸ ⟩
              p↑ * (q↓ * r↓) + p↓ * (q↑ * r↓ + q↓ * r↑)
            ∎

          ≃-denom = sym AA.assoc

  +-identityᴸ : AA.Identity AA.handᴸ _+_ 0
  +-identityᴸ = AA.identity +-identᴸ
    where
      +-identᴸ : {p : ℚ} → 0 + p ≃ p
      +-identᴸ {p↑ // p↓ ~ _} = ≃₀-intro (AA.[a≃b][c≃d] ≃-numer ≃-denom)
        where
          ≃-numer =
            begin
              0 * p↓ + 1 * p↑
            ≃⟨ AA.subst {f = _+ 1 * p↑} AA.absorb ⟩
              0 + 1 * p↑
            ≃⟨ AA.ident ⟩
              1 * p↑
            ≃⟨ AA.ident ⟩
              p↑
            ∎

          ≃-denom = sym AA.ident

  +-identityᴿ : AA.Identity AA.handᴿ _+_ 0
  +-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℚ}

  +-identity₂ : AA.Identity₂ _+_
  +-identity₂ = AA.identity₂ {A = ℚ}
