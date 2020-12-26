open import Function using (_∘_)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using
  (_≃_; Eq; refl; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for instance of ⊤
open import net.cruhland.models.Logic using ()

module net.cruhland.models.Integers.Equality (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
open import net.cruhland.models.Integers.Base PA as Base using (_—_; ℤ)

record _≃ᶻ_ (a b : ℤ) : Set where
  constructor ≃ᶻ-intro
  field
    elim : ℤ.pos a + ℤ.neg b ≃ ℤ.pos b + ℤ.neg a

≃ᶻ-refl : ∀ {a} → a ≃ᶻ a
≃ᶻ-refl = ≃ᶻ-intro refl

≃ᶻ-sym : ∀ {a b} → a ≃ᶻ b → b ≃ᶻ a
≃ᶻ-sym = ≃ᶻ-intro ∘ sym ∘ _≃ᶻ_.elim

instance
  ≃ᶻ-reflexive : Eq.Reflexive _≃ᶻ_
  ≃ᶻ-reflexive = record { refl = ≃ᶻ-intro refl }

  ≃ᶻ-symmetric : Eq.Symmetric _≃ᶻ_
  ≃ᶻ-symmetric = record { sym = ≃ᶻ-intro ∘ sym ∘ _≃ᶻ_.elim }

  ≃ᶻ-transitive : Eq.Transitive _≃ᶻ_
  ≃ᶻ-transitive = record { trans = ≃ᶻ-trans }
    where
      ≃ᶻ-trans : ∀ {a b c} → a ≃ᶻ b → b ≃ᶻ c → a ≃ᶻ c
      ≃ᶻ-trans
          {a⁺ — a⁻} {b⁺ — b⁻} {c⁺ — c⁻}
          (≃ᶻ-intro a⁺+b⁻≃b⁺+a⁻) (≃ᶻ-intro b⁺+c⁻≃c⁺+b⁻) =
            ≃ᶻ-intro (AA.cancelᴿ [a⁺+c⁻]+[b⁺+b⁻]≃[c⁺+a⁻]+[b⁺+b⁻])
        where
          [a⁺+c⁻]+[b⁺+b⁻]≃[c⁺+a⁻]+[b⁺+b⁻] =
            begin
              (a⁺ + c⁻) + (b⁺ + b⁻)
            ≃˘⟨ AA.perm-adcb ⟩
              (a⁺ + b⁻) + (b⁺ + c⁻)
            ≃⟨ AA.[a≃b][c≃d] a⁺+b⁻≃b⁺+a⁻ b⁺+c⁻≃c⁺+b⁻ ⟩
              (b⁺ + a⁻) + (c⁺ + b⁻)
            ≃⟨ AA.perm-adcb ⟩
              (b⁺ + b⁻) + (c⁺ + a⁻)
            ≃⟨ AA.comm ⟩
              (c⁺ + a⁻) + (b⁺ + b⁻)
            ∎

  eq : Eq ℤ
  eq = record { _≃_ = _≃ᶻ_ }

  from-ℕ-substitutive₁ : AA.Substitutive₁ {A = ℕ} (_as ℤ) _≃_ _≃_
  from-ℕ-substitutive₁ = record { subst = ≃ᶻ-intro ∘ AA.subst }

  from-ℕ-injective : AA.Injective {A = ℕ} _≃_ _≃_ (_as ℤ)
  from-ℕ-injective = record { inject = AA.cancelᴿ ∘ _≃ᶻ_.elim }

  ℤ-substitutiveᴸ : ∀ {m} → AA.Substitutive₁ (_— m) _≃_ _≃_
  ℤ-substitutiveᴸ {m} = record { subst = ℤ-substᴸ }
    where
      ℤ-substᴸ : ∀ {n₁ n₂} → n₁ ≃ n₂ → n₁ — m ≃ n₂ — m
      ℤ-substᴸ n₁≃n₂ = ≃ᶻ-intro (AA.subst n₁≃n₂)

  ℤ-substitutiveᴿ : ∀ {m} → AA.Substitutive₁ (m —_) _≃_ _≃_
  ℤ-substitutiveᴿ {m} = record { subst = ℤ-substᴿ }
    where
      ℤ-substᴿ : ∀ {n₁ n₂} → n₁ ≃ n₂ → m — n₁ ≃ m — n₂
      ℤ-substᴿ n₁≃n₂ = ≃ᶻ-intro (AA.subst (sym n₁≃n₂))

  ℤ-substitutive₂ : AA.Substitutive₂ _—_
  ℤ-substitutive₂ = record {}
