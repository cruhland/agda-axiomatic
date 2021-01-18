import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; _*_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.Multiplication (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers PA as ℤ using (ℤ)
import net.cruhland.models.Rationals.Addition PA as ℚ+
open import net.cruhland.models.Rationals.Base PA as ℚ using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as ℚ≃ using (≃₀-intro)
import net.cruhland.models.Rationals.Literals PA as ℚLit
import net.cruhland.models.Rationals.Negation PA as ℚ-

instance
  star : Op.Star ℚ
  star = record { _*_ = _*₀_ }
    where
      _*₀_ : ℚ → ℚ → ℚ
      (p↑ // p↓ ~ p↓≄0) *₀ (q↑ // q↓ ~ q↓≄0) =
        (p↑ * q↑) // p↓ * q↓ ~ AA.nonzero-prod p↓≄0 q↓≄0

neg-mult : {q : ℚ} → - q ≃ -1 * q
neg-mult {q↑ // q↓ ~ _} = ≃₀-intro (AA.[a≃b][c≃d] ℤ.neg-mult AA.ident)

instance
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
            ≃⟨ AA.subst {a₁ = a↑ * b↑} AA.comm ⟩
              b↑ * a↑ * (b↓ * a↓)
            ≃⟨ AA.subst {a₁ = b↓ * a↓} AA.comm ⟩
              b↑ * a↑ * (a↓ * b↓)
            ∎

  *-substitutiveᴸ : AA.Substitutiveᴸ _*_
  *-substitutiveᴸ {b@(b↑ // b↓ ~ _)} = AA.substitutive₁ *-substᴸ
    where
      *-substᴸ : {a₁ a₂ : ℚ} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
      *-substᴸ
        {a₁↑ // a₁↓ ~ _} {a₂↑ // a₂↓ ~ _} (≃₀-intro a₁↑a₂↓≃a₂↑a₁↓) =
          ≃₀-intro [a₁↑b↑][a₂↓b↓]≃[a₂↑b↑][a₁↓b↓]
        where
          [a₁↑b↑][a₂↓b↓]≃[a₂↑b↑][a₁↓b↓] =
            begin
              a₁↑ * b↑ * (a₂↓ * b↓)
            ≃⟨ AA.transpose ⟩
              a₁↑ * a₂↓ * (b↑ * b↓)
            ≃⟨ AA.subst a₁↑a₂↓≃a₂↑a₁↓ ⟩
              a₂↑ * a₁↓ * (b↑ * b↓)
            ≃˘⟨ AA.transpose ⟩
              a₂↑ * b↑ * (a₁↓ * b↓)
            ∎

  *-substitutiveᴿ : AA.Substitutiveᴿ _*_
  *-substitutiveᴿ = AA.substitutiveᴿ {A = ℚ}

  *-substitutive₂ : AA.Substitutive₂ _*_
  *-substitutive₂ = AA.substitutive₂ {A = ℚ}

  *-compatible-ℤ : AA.Compatible₂ (_as ℚ) _*_
  *-compatible-ℤ = AA.compatible₂ {A = ℤ} _*_ *-compat-ℤ
    where
      *-compat-ℤ : {a b : ℤ} → (a * b as ℚ) ≃ (a as ℚ) * (b as ℚ)
      *-compat-ℤ {a} {b} = ≃₀-intro (AA.subst {f = a * b *_} AA.identᴿ)

  *-associative : AA.Associative _*_
  *-associative = record { assoc = *-assoc }
    where
      *-assoc : {p q r : ℚ} → (p * q) * r ≃ p * (q * r)
      *-assoc {p↑ // p↓ ~ _} {q↑ // q↓ ~ _} {r↑ // r↓ ~ _} =
        ≃₀-intro (AA.[a≃b][c≃d] {_⊙_ = _*_} AA.assoc (sym AA.assoc))

  *-commutativeᴸ-neg : AA.Commutativeᴸ -_ _*_
  *-commutativeᴸ-neg = record { commᴸ = *-commᴸ-neg }
    where
      *-commᴸ-neg : {p q : ℚ} → (- p) * q ≃ - (p * q)
      *-commᴸ-neg {p} {q} =
        begin
          (- p) * q
        ≃⟨ AA.subst neg-mult ⟩
          (-1 * p) * q
        ≃⟨ AA.assoc ⟩
          -1 * (p * q)
        ≃˘⟨ neg-mult ⟩
          - (p * q)
        ∎

  *-commutativeᴿ-neg : AA.Commutativeᴿ {A = ℚ} -_ _*_
  *-commutativeᴿ-neg = AA.commutativeᴿ

  *-identityᴸ : AA.Identity AA.handᴸ _*_
  *-identityᴸ = AA.identity *-identᴸ
    where
      *-identᴸ : {p : ℚ} → 1 * p ≃ p
      *-identᴸ {p↑ // p↓ ~ _} =
        ≃₀-intro (AA.[a≃b][c≃d] {_⊙_ = _*_} AA.ident (sym AA.ident))

  *-identityᴿ : AA.Identity AA.handᴿ _*_
  *-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℚ}

  *-identity₂ : AA.Identity₂ _*_
  *-identity₂ = AA.identity₂ {A = ℚ}

  *-distributive-+ᴸ : AA.Distributive AA.handᴸ _*_ _+_
  *-distributive-+ᴸ = AA.distributive *-distrib-+ᴸ
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
            ≃˘⟨ AA.subst {f = _* a↓} AA.assoc ⟩
              (a↑ * b↑ * c↓) * a↓
            ≃⟨ AA.assoc ⟩
              a↑ * b↑ * (c↓ * a↓)
            ≃⟨ AA.subst {a₁ = c↓ * a↓} AA.comm ⟩
              a↑ * b↑ * (a↓ * c↓)
            ∎

          [a↑[b↓c↑]]a↓≃ab↓[a↑c↑] =
            begin
              (a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.comm ⟩
              a↓ * (a↑ * (b↓ * c↑))
            ≃˘⟨ AA.subst {f = a↓ *_} AA.assoc ⟩
              a↓ * (a↑ * b↓ * c↑)
            ≃⟨ AA.subst {f = a↓ *_} (AA.subst {f = _* c↑} AA.comm) ⟩
              a↓ * (b↓ * a↑ * c↑)
            ≃⟨ AA.subst {f = a↓ *_} AA.assoc ⟩
              a↓ * (b↓ * (a↑ * c↑))
            ≃˘⟨ AA.assoc ⟩
              a↓ * b↓ * (a↑ * c↑)
            ∎

          a↑[b↑c↓+b↓c↑]a↓≃a↑b↑[a↓c↓]+a↓b↓[a↑c↑] =
            begin
              a↑ * (b↑ * c↓ + b↓ * c↑) * a↓
            ≃⟨ AA.subst {f = _* a↓} AA.distrib ⟩
              (a↑ * (b↑ * c↓) + a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.distrib ⟩
              (a↑ * (b↑ * c↓)) * a↓ + (a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.[a≃b][c≃d] [a↑[b↑c↓]]a↓≃a↑b↑[a↓c↓] [a↑[b↓c↑]]a↓≃ab↓[a↑c↑] ⟩
              a↑ * b↑ * (a↓ * c↓) + a↓ * b↓ * (a↑ * c↑)
            ∎

          a[b+c]≃ab+ac =
            begin
              a↑ * (b↑ * c↓ + b↓ * c↑) * (a↓ * b↓ * (a↓ * c↓))
            ≃⟨ AA.subst a↓b↓[a↓c↓]≃a↓[a↓[b↓c↓]] ⟩
              a↑ * (b↑ * c↓ + b↓ * c↑) * (a↓ * (a↓ * (b↓ * c↓)))
            ≃˘⟨ AA.assoc ⟩
              a↑ * (b↑ * c↓ + b↓ * c↑) * a↓ * (a↓ * (b↓ * c↓))
            ≃⟨ AA.subst a↑[b↑c↓+b↓c↑]a↓≃a↑b↑[a↓c↓]+a↓b↓[a↑c↑] ⟩
              (a↑ * b↑ * (a↓ * c↓) + a↓ * b↓ * (a↑ * c↑)) * (a↓ * (b↓ * c↓))
            ∎

  *-distributive-+ᴿ : AA.Distributive AA.handᴿ _*_ _+_
  *-distributive-+ᴿ = AA.distributiveᴿ-from-distributiveᴸ {A = ℚ}
