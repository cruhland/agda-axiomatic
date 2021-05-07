import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.Addition (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
open import net.cruhland.models.Integers.Base PA as ℤ using (_—_; ℤ)
open import net.cruhland.models.Integers.Equality PA as ℤ≃ using (≃ᶻ-intro)

instance
  plus : Op.Plus ℤ
  plus = record { _+_ = _+₀_ }
    where
      infixl 6 _+₀_
      _+₀_ : ℤ → ℤ → ℤ
      a⁺ — a⁻ +₀ b⁺ — b⁻ = (a⁺ + b⁺) — (a⁻ + b⁻)

  +-commutative : AA.Commutative _+_
  +-commutative = AA.commutative +-comm
    where
      +-comm : {a b : ℤ} → a + b ≃ b + a
      +-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro eq′
        where
          eq′ =
            begin
              (a⁺ + b⁺) + (b⁻ + a⁻)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (b⁺ + a⁺) + (b⁻ + a⁻)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (b⁺ + a⁺) + (a⁻ + b⁻)
            ∎

  +-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≃_ _≃_
  +-substitutiveᴸ = AA.substitutive₂ +-substᴸ
    where
      +-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
      +-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} (≃ᶻ-intro a₁⁺+a₂⁻≃a₂⁺+a₁⁻) =
          ≃ᶻ-intro [a₁⁺+b⁺]+[a₂⁻+b⁻]≃[a₂⁺+b⁺]+[a₁⁻+b⁻]
        where
          [a₁⁺+b⁺]+[a₂⁻+b⁻]≃[a₂⁺+b⁺]+[a₁⁻+b⁻] =
            begin
              (a₁⁺ + b⁺) + (a₂⁻ + b⁻)
            ≃⟨ AA.transpose ⟩
              (a₁⁺ + a₂⁻) + (b⁺ + b⁻)
            ≃⟨ AA.subst₂ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
              (a₂⁺ + a₁⁻) + (b⁺ + b⁻)
            ≃⟨ AA.transpose ⟩
              (a₂⁺ + b⁺) + (a₁⁻ + b⁻)
            ∎

  +-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≃_ _≃_
  +-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm {A = ℤ}

  +-substitutive₂² : AA.Substitutive₂² _+_ _≃_ _≃_
  +-substitutive₂² = AA.substitutive₂² {A = ℤ}

  +-associative : AA.Associative _+_
  +-associative = record { assoc = +-assoc }
    where
      +-assoc : {x y z : ℤ} → (x + y) + z ≃ x + (y + z)
      +-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro eq′
        where
          eq′ =
            begin
              ((x⁺ + y⁺) + z⁺) + (x⁻ + (y⁻ + z⁻))
            ≃⟨ AA.subst₂ AA.assoc ⟩
              (x⁺ + (y⁺ + z⁺)) + (x⁻ + (y⁻ + z⁻))
            ≃˘⟨ AA.subst₂ AA.assoc ⟩
              (x⁺ + (y⁺ + z⁺)) + ((x⁻ + y⁻) + z⁻)
            ∎

  +-compatible-ℕ : AA.Compatible₂ (_as ℤ) _+_
  +-compatible-ℕ = AA.compatible₂ {A = ℕ} _+_ +-compat-ℕ
    where
      +-compat-ℕ : {n m : ℕ} → (n + m as ℤ) ≃ (n as ℤ) + (m as ℤ)
      +-compat-ℕ = ≃ᶻ-intro (AA.subst₂ AA.identᴸ)

  +-identityᴸ : AA.Identity AA.handᴸ _+_ 0
  +-identityᴸ = AA.identity +-identᴸ
    where
      +-identᴸ : {x : ℤ} → 0 + x ≃ x
      +-identᴸ {x⁺ — x⁻} = ≃ᶻ-intro [0+x⁺]+x⁻≃x⁺+[0+x⁻]
        where
          [0+x⁺]+x⁻≃x⁺+[0+x⁻] =
            begin
              0 + x⁺ + x⁻
            ≃⟨ AA.subst₂ AA.comm ⟩
              x⁺ + 0 + x⁻
            ≃⟨ AA.assoc ⟩
              x⁺ + (0 + x⁻)
            ∎

  +-identityᴿ : AA.Identity AA.handᴿ _+_ 0
  +-identityᴿ = AA.identityᴿ-from-identityᴸ {A = ℤ}

  +-identity₂ : AA.Identity₂ _+_
  +-identity₂ = AA.identity₂ {A = ℤ}
