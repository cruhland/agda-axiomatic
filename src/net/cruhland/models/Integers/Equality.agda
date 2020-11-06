open import Function using (_∘_)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using
  (_≃_; Eq; refl; sym; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for instance of ⊤
open import net.cruhland.models.Logic using ()

module net.cruhland.models.Integers.Equality (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
open import net.cruhland.models.Integers.Base PA using (_—_; ℤ)

record _≃ᶻ_ (a b : ℤ) : Set where
  constructor ≃ᶻ-intro
  field
    elim : ℤ.pos a + ℤ.neg b ≃ ℤ.pos b + ℤ.neg a

≃ᶻ-refl : ∀ {a} → a ≃ᶻ a
≃ᶻ-refl = ≃ᶻ-intro refl

≃ᶻ-sym : ∀ {a b} → a ≃ᶻ b → b ≃ᶻ a
≃ᶻ-sym = ≃ᶻ-intro ∘ sym ∘ _≃ᶻ_.elim

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

instance
  eq : Eq ℤ
  eq = record
    { _≃_ = _≃ᶻ_
    ; refl = ≃ᶻ-refl
    ; sym = ≃ᶻ-sym
    ; trans = ≃ᶻ-trans
    }
