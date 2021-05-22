import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.models.Integers.NatPair.PropertiesImpl
  (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (_—_; ℤ; ≃₀-intro)

-- Export the definitions from the default implementation
open import net.cruhland.axioms.Integers.PropertiesImplBase PA ZB public

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
