-- Needed for positive integer literals (typeclass)
import Agda.Builtin.FromNat
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for positive integer literals (instance for ⊤)
import net.cruhland.models.Logic

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

  *-associative : AA.Associative _*_
  *-associative = record { assoc = *-assoc }
    where
      *-assoc : {p q r : ℚ} → (p * q) * r ≃ p * (q * r)
      *-assoc {p↑ // p↓ ~ _} {q↑ // q↓ ~ _} {r↑ // r↓ ~ _} =
        ≃₀-intro (AA.[a≃b][c≃d] (AA.assoc {_⊙_ = _*_}) (sym AA.assoc))

  *-identityᴸ : AA.Identityᴸ _*_ 1
  *-identityᴸ = record { identᴸ = *-identᴸ }
    where
      *-identᴸ : {p : ℚ} → 1 * p ≃ p
      *-identᴸ {p↑ // p↓ ~ _} =
        ≃₀-intro (AA.[a≃b][c≃d] (AA.identᴸ {_⊙_ = _*_}) (sym AA.identᴸ))

  *-identityᴿ : AA.Identityᴿ {A = ℚ} _*_ 1
  *-identityᴿ = AA.identityᴿ

  *-distributive-+ᴸ : AA.Distributiveᴸ _*_ _+_
  *-distributive-+ᴸ = record { distribᴸ = *-distrib-+ᴸ }
    where
      *-distrib-+ᴸ : {a b c : ℚ} → a * (b + c) ≃ a * b + a * c
      *-distrib-+ᴸ {a↑ // a↓ ~ _} {b↑ // b↓ ~ _} {c↑ // c↓ ~ _} =
          ≃₀-intro a[b+c]≃ab+ac
        where
          a↓b↓[a↓c↓]≃a↓[a↓[b↓c↓]] =
            begin
              a↓ * b↓ * (a↓ * c↓)
            ≃⟨ AA.transpose ⟩
              a↓ * a↓ * (b↓ * c↓)
            ≃⟨ AA.assoc ⟩
              a↓ * (a↓ * (b↓ * c↓))
            ∎

          [a↑[b↑c↓]]a↓≃a↑b↑[a↓c↓] =
            begin
              (a↑ * (b↑ * c↓)) * a↓
            ≃˘⟨ AA.substᴸ AA.assoc ⟩
              (a↑ * b↑ * c↓) * a↓
            ≃⟨ AA.assoc ⟩
              a↑ * b↑ * (c↓ * a↓)
            ≃⟨ AA.substᴿ AA.comm ⟩
              a↑ * b↑ * (a↓ * c↓)
            ∎

          [a↑[b↓c↑]]a↓≃ab↓[a↑c↑] =
            begin
              (a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.comm ⟩
              a↓ * (a↑ * (b↓ * c↑))
            ≃˘⟨ AA.substᴿ AA.assoc ⟩
              a↓ * (a↑ * b↓ * c↑)
            ≃⟨ AA.substᴿ (AA.substᴸ AA.comm) ⟩
              a↓ * (b↓ * a↑ * c↑)
            ≃⟨ AA.substᴿ AA.assoc ⟩
              a↓ * (b↓ * (a↑ * c↑))
            ≃˘⟨ AA.assoc ⟩
              a↓ * b↓ * (a↑ * c↑)
            ∎

          a↑[b↑c↓+b↓c↑]a↓≃a↑b↑[a↓c↓]+a↓b↓[a↑c↑] =
            begin
              a↑ * (b↑ * c↓ + b↓ * c↑) * a↓
            ≃⟨ AA.substᴸ AA.distribᴸ ⟩
              (a↑ * (b↑ * c↓) + a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.distribᴿ ⟩
              (a↑ * (b↑ * c↓)) * a↓ + (a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.[a≃b][c≃d] [a↑[b↑c↓]]a↓≃a↑b↑[a↓c↓] [a↑[b↓c↑]]a↓≃ab↓[a↑c↑] ⟩
              a↑ * b↑ * (a↓ * c↓) + a↓ * b↓ * (a↑ * c↑)
            ∎

          a[b+c]≃ab+ac =
            begin
              a↑ * (b↑ * c↓ + b↓ * c↑) * (a↓ * b↓ * (a↓ * c↓))
            ≃⟨ AA.substᴿ a↓b↓[a↓c↓]≃a↓[a↓[b↓c↓]] ⟩
              a↑ * (b↑ * c↓ + b↓ * c↑) * (a↓ * (a↓ * (b↓ * c↓)))
            ≃˘⟨ AA.assoc ⟩
              a↑ * (b↑ * c↓ + b↓ * c↑) * a↓ * (a↓ * (b↓ * c↓))
            ≃⟨ AA.substᴸ a↑[b↑c↓+b↓c↑]a↓≃a↑b↑[a↓c↓]+a↓b↓[a↑c↑] ⟩
              (a↑ * b↑ * (a↓ * c↓) + a↓ * b↓ * (a↑ * c↑)) * (a↓ * (b↓ * c↓))
            ∎

  *-distributive-+ᴿ : AA.Distributiveᴿ {A = ℚ} _*_ _+_
  *-distributive-+ᴿ = AA.distributiveᴿ
