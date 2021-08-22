import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_; _*_; _⁻¹)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (contrapositive)

module net.cruhland.models.Rationals.IntPair.ReciprocalImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

private
  module ℤ = Integers Z
  module ℚ where
    open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public
    open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
    open import net.cruhland.models.Rationals.IntPair.MultiplicationImpl PA Z
      public
    open import net.cruhland.models.Rationals.IntPair.NegationImpl PA Z public

open ℚ using (ℚ; _//_)

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

  recip-compat-neg : AA.Compatible₁ _⁻¹ -_ -_ _≃_
  recip-compat-neg = AA.compatible₁ recip-neg
    where
      recip-neg : {q : ℚ} {{c₁ : q ≄ 0}} {{c₂ : - q ≄ 0}} → (- q) ⁻¹ ≃ - (q ⁻¹)
      recip-neg q@{q↑ // q↓} {{q≄0}} {{ -q≄0 }} =
        let instance
              q↑≄0 = contrapositive ℚ.q≃0-from-q↑≃0 q≄0
              -q↑≄0 = contrapositive ℚ.q≃0-from-q↑≃0 -q≄0
         in begin
              (- q) ⁻¹
            ≃⟨⟩
              (- (q↑ // q↓)) ⁻¹
            ≃⟨⟩
              ((- q↑) // q↓) ⁻¹
            ≃⟨⟩
              q↓ // (- q↑)
            ≃˘⟨ AA.fnOpCommᴿ ⟩
              - (q↓ // q↑)
            ≃⟨⟩
              - (q ⁻¹)
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

  recip-compat-* : AA.Compatible₂ _⁻¹ _*_ _*_ _≃_
  recip-compat-* = AA.compatible₂ *-recip
    where
      *-recip :
        {p q : ℚ} {{pq≄0 : p * q ≄ 0}} {{p≄0 : p ≄ 0}} {{q≄0 : q ≄ 0}} →
        (p * q) ⁻¹ ≃ p ⁻¹ * q ⁻¹
      *-recip
          p@{(p↑ // p↓) {{p↓≄0}}} q@{(q↑ // q↓) {{q↓≄0}}}
          {{pq≄0}} {{p≄0}} {{q≄0}} =
        let instance
              p↑≄0 = contrapositive ℚ.q≃0-from-q↑≃0 p≄0
              q↑≄0 = contrapositive ℚ.q≃0-from-q↑≃0 q≄0
              p↑q↑≄0₁ = contrapositive ℚ.q≃0-from-q↑≃0 pq≄0
              p↑q↑≄0₂ = AA.nonzero-prod {{a≄0 = p↑≄0}} {{q↑≄0}}
              p↓q↓≄0 = AA.nonzero-prod {{a≄0 = p↓≄0}} {{q↓≄0}}
         in begin
              (p * q) ⁻¹
            ≃⟨⟩
              ((p↑ // p↓) * (q↑ // q↓)) ⁻¹
            ≃⟨⟩
              ((p↑ * q↑) // (p↓ * q↓)) ⁻¹
            ≃⟨⟩
              ((p↓ * q↓) // (p↑ * q↑)) {{p↑q↑≄0₁}}
            ≃⟨ ℚ.≃₀-intro Eq.refl ⟩
              ((p↓ * q↓) // (p↑ * q↑)) {{p↑q↑≄0₂}}
            ≃⟨⟩
              (p↓ // p↑) * (q↓ // q↑)
            ≃⟨⟩
              (p↑ // p↓) ⁻¹ * (q↑ // q↓) ⁻¹
            ≃⟨⟩
              p ⁻¹ * q ⁻¹
            ∎
