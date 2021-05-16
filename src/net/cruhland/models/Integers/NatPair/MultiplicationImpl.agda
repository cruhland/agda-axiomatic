import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers.NatPair.MultiplicationImpl
  (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤ
  using (_—_; ℤ; ≃₀-intro)

instance
  star : Op.Star ℤ
  star = Op.star _*₀_
    where
      _*₀_ : ℤ → ℤ → ℤ
      (a⁺ — a⁻) *₀ (b⁺ — b⁻) = (a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)

  *-commutative : AA.Commutative _*_
  *-commutative = AA.commutative *-comm
    where
      *-comm : {a b : ℤ} → a * b ≃ b * a
      *-comm {a⁺ — a⁻} {b⁺ — b⁻} =
        let ab≃ba =
              begin
                (a⁺ * b⁺ + a⁻ * b⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
              ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
                (b⁺ * a⁺ + a⁻ * b⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
              ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
                (b⁺ * a⁺ + b⁻ * a⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
              ≃⟨ AA.subst₂ AA.comm ⟩
                (b⁺ * a⁺ + b⁻ * a⁻) + (b⁻ * a⁺ + b⁺ * a⁻)
              ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
                (b⁺ * a⁺ + b⁻ * a⁻) + (a⁺ * b⁻ + b⁺ * a⁻)
              ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
                (b⁺ * a⁺ + b⁻ * a⁻) + (a⁺ * b⁻ + a⁻ * b⁺)
              ∎
         in ≃₀-intro ab≃ba
