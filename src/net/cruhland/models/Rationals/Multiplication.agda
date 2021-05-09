import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; _*_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Rationals.Multiplication (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.models.Integers PA as ℤ using (ℤ)
import net.cruhland.models.Rationals.Addition PA as ℚ+
open import net.cruhland.models.Rationals.Base PA as ℚ using (_//_~_; ℚ)
open import net.cruhland.models.Rationals.Equality PA as ℚ≃ using (≃₀-intro)
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
  *-commutative = AA.commutative *-comm
    where
      *-comm : {a b : ℚ} → a * b ≃ b * a
      *-comm {a↑ // a↓ ~ _} {b↑ // b↓ ~ _} =
          ≃₀-intro [a↑b↑][b↓a↓]≃[b↑a↑][a↓b↓]
        where
          [a↑b↑][b↓a↓]≃[b↑a↑][a↓b↓] =
            begin
              a↑ * b↑ * (b↓ * a↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              b↑ * a↑ * (b↓ * a↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              b↑ * a↑ * (a↓ * b↓)
            ∎

  *-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _*_ _≃_ _≃_
  *-substitutiveᴸ = AA.substitutive₂ *-substᴸ
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
            ≃⟨ AA.subst₂ a₁↑a₂↓≃a₂↑a₁↓ ⟩
              a₂↑ * a₁↓ * (b↑ * b↓)
            ≃˘⟨ AA.transpose ⟩
              a₂↑ * b↑ * (a₁↓ * b↓)
            ∎

  *-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _*_ _≃_ _≃_
  *-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm {A = ℚ}

  *-substitutive₂ : AA.Substitutive₂² _*_ _≃_ _≃_
  *-substitutive₂ = AA.substitutive₂² {A = ℚ}

  *-compatible-ℤ : AA.Compatible₂ (_as ℚ) _*_
  *-compatible-ℤ = AA.compatible₂ {A = ℤ} _*_ *-compat-ℤ
    where
      *-compat-ℤ : {a b : ℤ} → (a * b as ℚ) ≃ (a as ℚ) * (b as ℚ)
      *-compat-ℤ {a} {b} = ≃₀-intro (AA.subst₂ AA.identᴿ)

  *-associative : AA.Associative _*_
  *-associative = record { assoc = *-assoc }
    where
      *-assoc : {p q r : ℚ} → (p * q) * r ≃ p * (q * r)
      *-assoc {p↑ // p↓ ~ _} {q↑ // q↓ ~ _} {r↑ // r↓ ~ _} =
        ≃₀-intro (AA.[a≃b][c≃d] {_⊙_ = _*_} AA.assoc (sym AA.assoc))

  *-fnOpCommutativeᴸ-neg : AA.FnOpCommutative AA.handᴸ -_ _*_
  *-fnOpCommutativeᴸ-neg = AA.fnOpCommutative *-commᴸ-neg
    where
      *-commᴸ-neg : {p q : ℚ} → - (p * q) ≃ (- p) * q
      *-commᴸ-neg {p} {q} =
        begin
          - (p * q)
        ≃⟨ neg-mult ⟩
          -1 * (p * q)
        ≃˘⟨ AA.assoc ⟩
          (-1 * p) * q
        ≃˘⟨ AA.subst₂ neg-mult ⟩
          (- p) * q
        ∎

  *-fnOpCommutativeᴿ-neg : AA.FnOpCommutative AA.handᴿ -_ _*_
  *-fnOpCommutativeᴿ-neg = AA.fnOpCommutativeᴿ-from-fnOpCommutativeᴸ {A = ℚ}

  *-identityᴸ : AA.Identity AA.handᴸ _*_ 1
  *-identityᴸ = AA.identity *-identᴸ
    where
      *-identᴸ : {p : ℚ} → 1 * p ≃ p
      *-identᴸ {p↑ // p↓ ~ _} =
        ≃₀-intro (AA.[a≃b][c≃d] {_⊙_ = _*_} AA.ident (sym AA.ident))

  *-identityᴿ : AA.Identity AA.handᴿ _*_ 1
  *-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℚ}

  *-identity₂ : AA.Identity₂ _*_ 1
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
            ≃˘⟨ AA.subst₂ AA.assoc ⟩
              (a↑ * b↑ * c↓) * a↓
            ≃⟨ AA.assoc ⟩
              a↑ * b↑ * (c↓ * a↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              a↑ * b↑ * (a↓ * c↓)
            ∎

          [a↑[b↓c↑]]a↓≃ab↓[a↑c↑] =
            begin
              (a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.comm ⟩
              a↓ * (a↑ * (b↓ * c↑))
            ≃˘⟨ AA.subst₂ AA.assoc ⟩
              a↓ * (a↑ * b↓ * c↑)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              a↓ * (b↓ * a↑ * c↑)
            ≃⟨ AA.subst₂ AA.assoc ⟩
              a↓ * (b↓ * (a↑ * c↑))
            ≃˘⟨ AA.assoc ⟩
              a↓ * b↓ * (a↑ * c↑)
            ∎

          a↑[b↑c↓+b↓c↑]a↓≃a↑b↑[a↓c↓]+a↓b↓[a↑c↑] =
            begin
              a↑ * (b↑ * c↓ + b↓ * c↑) * a↓
            ≃⟨ AA.subst₂ AA.distrib ⟩
              (a↑ * (b↑ * c↓) + a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.distrib ⟩
              (a↑ * (b↑ * c↓)) * a↓ + (a↑ * (b↓ * c↑)) * a↓
            ≃⟨ AA.[a≃b][c≃d] [a↑[b↑c↓]]a↓≃a↑b↑[a↓c↓] [a↑[b↓c↑]]a↓≃ab↓[a↑c↑] ⟩
              a↑ * b↑ * (a↓ * c↓) + a↓ * b↓ * (a↑ * c↑)
            ∎

          a[b+c]≃ab+ac =
            begin
              a↑ * (b↑ * c↓ + b↓ * c↑) * (a↓ * b↓ * (a↓ * c↓))
            ≃⟨ AA.subst₂ a↓b↓[a↓c↓]≃a↓[a↓[b↓c↓]] ⟩
              a↑ * (b↑ * c↓ + b↓ * c↑) * (a↓ * (a↓ * (b↓ * c↓)))
            ≃˘⟨ AA.assoc ⟩
              a↑ * (b↑ * c↓ + b↓ * c↑) * a↓ * (a↓ * (b↓ * c↓))
            ≃⟨ AA.subst₂ a↑[b↑c↓+b↓c↑]a↓≃a↑b↑[a↓c↓]+a↓b↓[a↑c↑] ⟩
              (a↑ * b↑ * (a↓ * c↓) + a↓ * b↓ * (a↑ * c↑)) * (a↓ * (b↓ * c↓))
            ∎

  *-distributive-+ᴿ : AA.Distributive AA.handᴿ _*_ _+_
  *-distributive-+ᴿ = AA.distributiveᴿ-from-distributiveᴸ {A = ℚ}
