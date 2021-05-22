import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.models.Integers.NatPair.Negation.BaseImpl
  (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
import net.cruhland.models.Integers.NatPair.AdditionImpl PA as ℤ+
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (_—_; ℤ; ≃₀-intro)
import net.cruhland.models.Integers.NatPair.PropertiesImpl PA as ℤP

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

  neg-inverseᴸ : AA.Inverse AA.handᴸ -_ (const ⊤) _+_ 0
  neg-inverseᴸ = AA.inverse neg-invᴸ
    where
      neg-invᴸ : {x : ℤ} → - x + x ≃ 0
      neg-invᴸ {x⁺ — x⁻} = ≃₀-intro [x⁻+x⁺]+0≃0+[x⁺+x⁻]
        where
          [x⁻+x⁺]+0≃0+[x⁺+x⁻] =
            begin
              (x⁻ + x⁺) + 0
            ≃⟨ AA.comm ⟩
              0 + (x⁻ + x⁺)
            ≃⟨ AA.subst₂ AA.comm ⟩
              0 + (x⁺ + x⁻)
            ∎

  neg-inverseᴿ : AA.Inverse AA.handᴿ -_ (const ⊤) _+_ 0
  neg-inverseᴿ = AA.inverseᴿ-from-inverseᴸ

  neg-inverse : AA.Inverse² -_ (const ⊤) _+_ 0
  neg-inverse = AA.inverse²
