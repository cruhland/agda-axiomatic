import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Integers.NatPair.BaseImpl as BaseImpl

module net.cruhland.models.Integers.NatPair.NegationImpl
  (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
private open module ℤ = BaseImpl PA using (_—_; ℤ; ≃₀-intro)

instance
  neg-dash : Op.Dashᴸ ℤ
  neg-dash = Op.dashᴸ λ { (x⁺ — x⁻) → x⁻ — x⁺ }

  neg-substitutive : AA.Substitutive₁ -_ _≃_ _≃_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : {a b : ℤ} → a ≃ b → - a ≃ - b
      neg-subst {a⁺ — a⁻} {b⁺ — b⁻} (≃₀-intro a⁺+b⁻≃b⁺+a⁻) =
          ≃₀-intro a⁻+b⁺≃b⁻+a⁺
        where
          a⁻+b⁺≃b⁻+a⁺ =
            begin
              a⁻ + b⁺
            ≃⟨ AA.comm ⟩
              b⁺ + a⁻
            ≃˘⟨ a⁺+b⁻≃b⁺+a⁻ ⟩
              a⁺ + b⁻
            ≃⟨ AA.comm ⟩
              b⁻ + a⁺
            ∎
