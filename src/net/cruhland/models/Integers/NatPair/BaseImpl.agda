import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast as Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.NatPair.BaseImpl
  (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)

infix 9 _—_
record ℤ : Set where
  constructor _—_
  field
    pos neg : ℕ

record _≃₀_ (a b : ℤ) : Set where
  constructor ≃₀-intro
  field
    elim : ℤ.pos a + ℤ.neg b ≃ ℤ.pos b + ℤ.neg a

instance
  ≃₀-reflexive : Eq.Reflexive _≃₀_
  ≃₀-reflexive = Eq.reflexive (≃₀-intro Eq.refl)

  ≃₀-symmetric : Eq.Symmetric _≃₀_
  ≃₀-symmetric =
    Eq.symmetric λ { (≃₀-intro a⁺+b⁻≃b⁺+a⁻) → ≃₀-intro (Eq.sym a⁺+b⁻≃b⁺+a⁻) }

  ≃₀-transitive : Eq.Transitive _≃₀_
  ≃₀-transitive = Eq.transitive ≃₀-trans
    where
      ≃₀-trans : ∀ {a b c} → a ≃₀ b → b ≃₀ c → a ≃₀ c
      ≃₀-trans
          {a⁺ — a⁻} {b⁺ — b⁻} {c⁺ — c⁻}
          (≃₀-intro a⁺+b⁻≃b⁺+a⁻) (≃₀-intro b⁺+c⁻≃c⁺+b⁻) =
            ≃₀-intro (AA.cancel [a⁺+c⁻]+[b⁺+b⁻]≃[c⁺+a⁻]+[b⁺+b⁻])
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
  eq = Eq.equivalence _≃₀_

  ℤ-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _—_ _≃_ _≃_
  ℤ-substitutiveᴸ = AA.substitutive₂ (≃₀-intro ∘ AA.subst₂)

  ℤ-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _—_ _≃_ _≃_
  ℤ-substitutiveᴿ = AA.substitutive₂ (≃₀-intro ∘ AA.subst₂ ∘ Eq.sym)

  ℤ-substitutive : AA.Substitutive² _—_ _≃_ _≃_
  ℤ-substitutive = AA.substitutive²

  private
    ℤ-cancellativeᴸ : AA.Cancellative AA.handᴸ _—_ _≃_ _≃_
    ℤ-cancellativeᴸ =
      AA.cancellative λ {p n₁ n₂} → Eq.sym ∘ AA.cancel ∘ _≃₀_.elim

    ℤ-cancellativeᴿ : AA.Cancellative AA.handᴿ _—_ _≃_ _≃_
    ℤ-cancellativeᴿ = AA.cancellative λ {p n₁ n₂} → AA.cancel ∘ _≃₀_.elim

  ℤ-cancellative : AA.Cancellative² _—_ _≃_ _≃_
  ℤ-cancellative = AA.cancellative²

  from-ℕ : ℕ As ℤ
  from-ℕ = Cast.As-intro (_— 0)

  from-ℕ-substitutive₁ : AA.Substitutive₁ (_as ℤ) _≃_ _≃_
  from-ℕ-substitutive₁ = AA.substitutive₁ {A = ℕ} AA.subst₂

  from-ℕ-injective : AA.Injective (_as ℤ) _≃_ _≃_
  from-ℕ-injective = AA.injective {A = ℕ} AA.cancel

-- Pull in literals from the partial impl
import net.cruhland.axioms.Integers.BasePartialImpl PA as ZB
open ZB.BaseProperties (record { ℤ = ℤ }) public hiding (ℤ; eq; from-ℕ)

zero-from-balanced : ∀ {x} → ℤ.pos x ≃ ℤ.neg x → x ≃ 0
zero-from-balanced {x⁺ — x⁻} x⁺≃x⁻ =
  let x⁺+0≃0+x⁻ =
        begin
          x⁺ + 0
        ≃⟨ AA.ident ⟩
          x⁺
        ≃⟨ x⁺≃x⁻ ⟩
          x⁻
        ≃˘⟨ AA.ident ⟩
          0 + x⁻
        ∎
   in ≃₀-intro x⁺+0≃0+x⁻

balanced-from-zero : ∀ {x} → x ≃ 0 → ℤ.pos x ≃ ℤ.neg x
balanced-from-zero {x⁺ — x⁻} (≃₀-intro x⁺+0≃0+x⁻) =
  begin
    x⁺
  ≃˘⟨ AA.ident ⟩
    x⁺ + 0
  ≃⟨ x⁺+0≃0+x⁻ ⟩
    0 + x⁻
  ≃⟨ AA.ident ⟩
    x⁻
  ∎
