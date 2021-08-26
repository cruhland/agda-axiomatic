import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.NatPair.NegationImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (ZA)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)

private
  module ℕ = PeanoArithmetic PA
  module ℤ where
    open import net.cruhland.axioms.Integers.LiteralImpl PA ZB public
    open import net.cruhland.models.Integers.NatPair.AdditionImpl PA public
    open import net.cruhland.models.Integers.NatPair.BaseImpl PA public

open ℤ using (_—_; ℤ)

instance
  neg-dash : Op.Dashᴸ ℤ
  neg-dash = Op.dashᴸ λ { (x⁺ — x⁻) → x⁻ — x⁺ }

  neg-substitutive : AA.Substitutive₁ -_ _≃_ _≃_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : {a b : ℤ} → a ≃ b → - a ≃ - b
      neg-subst {a⁺ — a⁻} {b⁺ — b⁻} (ℤ.≃₀-intro a⁺+b⁻≃b⁺+a⁻) =
          ℤ.≃₀-intro a⁻+b⁺≃b⁻+a⁺
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

  neg-inverseᴸ : AA.Inverse AA.handᴸ (AA.tc₁ λ a → - a) _+_ 0
  neg-inverseᴸ = AA.inverse neg-invᴸ
    where
      neg-invᴸ : {x : ℤ} → - x + x ≃ 0
      neg-invᴸ {x⁺ — x⁻} = ℤ.≃₀-intro [x⁻+x⁺]+0≃0+[x⁺+x⁻]
        where
          [x⁻+x⁺]+0≃0+[x⁺+x⁻] =
            begin
              (x⁻ + x⁺) + 0
            ≃⟨ AA.comm ⟩
              0 + (x⁻ + x⁺)
            ≃⟨ AA.subst₂ AA.comm ⟩
              0 + (x⁺ + x⁻)
            ∎

  neg-inverseᴿ : AA.Inverse AA.handᴿ (AA.tc₁ λ a → - a) _+_ 0
  neg-inverseᴿ = AA.inverseᴿ-from-inverseᴸ

  neg-inverse : AA.Inverse² (AA.tc₁ λ a → - a) _+_ 0
  neg-inverse = AA.inverse²

  sub-dash : Op.Dash₂ ℤ
  sub-dash = Op.subtraction

sub-defn : {a b : ℤ} → a - b ≃ a + (- b)
sub-defn = Eq.refl

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive a@{a⁺ — a⁻} =
  begin
    - (- a)
  ≃⟨⟩
    - (- (a⁺ — a⁻))
  ≃⟨⟩
    - (a⁻ — a⁺)
  ≃⟨⟩
    a⁺ — a⁻
  ≃⟨⟩
    a
  ∎

-- Export everything not defined here from the default implementations
private
  open import net.cruhland.axioms.Integers.NegationPartialImpl PA
    using (NegationProperties)
  open import net.cruhland.axioms.Integers.NegationPartialImplSub PA
    using (SubtractionProperties)

  negationProperties : NegationProperties ZB ZA
  negationProperties = record {}

  subtractionProperties : SubtractionProperties ZB ZA
  subtractionProperties = record { sub-defn = sub-defn }

open NegationProperties negationProperties public
  hiding (neg-dash; neg-inverse; neg-substitutive)
open SubtractionProperties subtractionProperties public
  hiding (neg-dash; neg-inverse; neg-substitutive; sub-dash; sub-defn)
