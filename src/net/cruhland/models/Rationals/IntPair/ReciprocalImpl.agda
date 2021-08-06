import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_*_; _/_; _⁻¹)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contrapositive)

module net.cruhland.models.Rationals.IntPair.ReciprocalImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.AdditionDefn PA Z using (QA)
open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)
open import net.cruhland.models.Rationals.IntPair.MultiplicationDefn PA Z
  using (QM)

private module ℤ = Integers Z
private module ℚ where
  open import net.cruhland.models.Rationals.IntPair.AdditionImpl PA Z public
  open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public
  open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
  open import net.cruhland.models.Rationals.IntPair.MultiplicationImpl PA Z
    public

open ℤ using (ℤ)
open ℚ using (_//_; ℚ)

_⁻¹₀ : (q : ℚ) {{_ : q ≄ 0}} → ℚ
_⁻¹₀ (q↑ // q↓) {{q≄0}} = (q↓ // q↑) {{contrapositive ℚ.q≃0-from-q↑≃0 q≄0}}

instance
  reciprocal : Op.SupNegOne ℚ (_≄ 0)
  reciprocal = Op.supNegOne _⁻¹₀

  recip-substitutive : AA.Substitutive₁ᶜ {A = ℚ} _⁻¹ _≃_ _≃_
  recip-substitutive = AA.substitutive₁ recip-subst
    where
      recip-subst :
        {q₁ q₂ : ℚ} {{_ : q₁ ≄ 0}} {{_ : q₂ ≄ 0}} → q₁ ≃ q₂ → q₁ ⁻¹ ≃ q₂ ⁻¹
      recip-subst
        q₁@{q₁↑ // q₁↓} q₂@{q₂↑ // q₂↓} {{q₁≄0}} {{q₂≄0}}
        (ℚ.≃₀-intro q₁↑q₂↓≃q₂↑q₁↓) =
          begin
            q₁ ⁻¹
          ≃⟨⟩
            (q₁↑ // q₁↓) ⁻¹
          ≃⟨⟩
            (q₁↓ // q₁↑) {{contrapositive ℚ.q≃0-from-q↑≃0 q₁≄0}}
          ≃⟨ ℚ.≃₀-intro componentEq ⟩
            (q₂↓ // q₂↑) {{contrapositive ℚ.q≃0-from-q↑≃0 q₂≄0}}
          ≃⟨⟩
            (q₂↑ // q₂↓) ⁻¹
          ≃⟨⟩
            q₂ ⁻¹
          ∎
        where
          componentEq =
            begin
              q₁↓ * q₂↑
            ≃⟨ AA.comm ⟩
              q₂↑ * q₁↓
            ≃˘⟨ q₁↑q₂↓≃q₂↑q₁↓ ⟩
              q₁↑ * q₂↓
            ≃⟨ AA.comm ⟩
              q₂↓ * q₁↑
            ∎

  *-inverseᴸ : AA.Inverse AA.handᴸ _⁻¹ _*_ 1
  *-inverseᴸ = AA.inverse *-invᴸ
    where
      *-invᴸ : {q : ℚ} {{_ : q ≄ 0}} → q ⁻¹ * q ≃ 1
      *-invᴸ q@{(q↑ // q↓) {{q↓≄0}}} {{q≄0}} =
        let instance
              q↑≄0 = contrapositive ℚ.q≃0-from-q↑≃0 q≄0
              q↑q↓≄0 = AA.nonzero-prod {{a≄0 = q↑≄0}} {{q↓≄0}}
         in begin
              q ⁻¹ * q
            ≃⟨⟩
              (q↑ // q↓) ⁻¹ * (q↑ // q↓)
            ≃⟨⟩
              (q↓ // q↑) * (q↑ // q↓)
            ≃⟨⟩
              (q↓ * q↑) // (q↑ * q↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (q↑ * q↓) // (q↑ * q↓)
            ≃⟨ ℚ.a//a≃1 ⟩
              1
            ∎

  *-inverseᴿ : AA.Inverse AA.handᴿ _⁻¹ _*_ 1
  *-inverseᴿ = AA.inverseᴿ-from-inverseᴸ

  *-inverse : AA.Inverse² _⁻¹ _*_ 1
  *-inverse = AA.inverse²

-- Export everything not defined here from the partial implementation
private
  open import net.cruhland.axioms.Rationals.ReciprocalPartialImpl PA Z
    using (ReciprocalProperties)

  reciprocalProperties : ReciprocalProperties QB QA QM
  reciprocalProperties = record {}

open ReciprocalProperties reciprocalProperties public hiding (reciprocal)

a:ℚ/b:ℚ≃a//b :
  {a b : ℤ} {{b≄0 : b ≄ 0}} →
  let instance b:ℚ≄0:ℚ = AA.subst₁ b≄0 in (a as ℚ) / (b as ℚ) ≃ a // b
a:ℚ/b:ℚ≃a//b {a} {b} {{b≄0}} =
  let instance
        b:ℚ≄0:ℚ = AA.subst₁ b≄0
        1*b≄0 = AA.nonzero-prod {{a≄0 = ℤ.1≄0}} {{b≄0}}
   in begin
        (a as ℚ) / (b as ℚ)
      ≃⟨⟩
        (a // 1) / (b // 1)
      ≃⟨⟩
        (a // 1) * (b // 1) ⁻¹
      ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
        (a // 1) * (1 // b)
      ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
        (a * 1) // (1 * b)
      ≃⟨ AA.subst₂ AA.ident ⟩
        a // (1 * b)
      ≃⟨ AA.subst₂ AA.ident ⟩
        a // b
      ∎
