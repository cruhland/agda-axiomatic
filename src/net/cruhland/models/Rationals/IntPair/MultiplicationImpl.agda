import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.MultiplicationImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z as ℚB
  using (_//_; ℚ)

_*₀_ : ℚ → ℚ → ℚ
(p↑ // p↓) *₀ (q↑ // q↓) = ((p↑ * q↑) // (p↓ * q↓)) {{AA.nonzero-prodⁱ}}

instance
  star : Op.Star ℚ
  star = Op.star _*₀_

  *-commutative : AA.Commutative _*_
  *-commutative = AA.commutative *-comm
    where
      *-comm : {p q : ℚ} → p * q ≃ q * p
      *-comm p@{(p↑ // p↓) {{p↓≄ⁱ0}}} q@{(q↑ // q↓) {{q↓≄ⁱ0}}} =
        let instance p↓q↓≄ⁱ0 = AA.nonzero-prodⁱ {{ca = p↓≄ⁱ0}} {{cb = q↓≄ⁱ0}}
            instance q↓p↓≄ⁱ0 = AA.nonzero-prodⁱ {{ca = q↓≄ⁱ0}} {{cb = p↓≄ⁱ0}}
         in begin
              p * q
            ≃⟨⟩
              (p↑ // p↓) * (q↑ // q↓)
            ≃⟨⟩
              (p↑ * q↑) // (p↓ * q↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (q↑ * p↑) // (p↓ * q↓)
            ≃⟨ AA.subst₂ AA.comm ⟩
              (q↑ * p↑) // (q↓ * p↓)
            ≃⟨⟩
              (q↑ // q↓) * (p↑ // p↓)
            ≃⟨⟩
              q * p
            ∎

  *-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _*_ _≃_ _≃_
  *-substitutiveᴸ = AA.substitutive₂ *-substᴸ
    where
      *-substᴸ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → p₁ * q ≃ p₂ * q
      *-substᴸ
        p₁@{p₁↑ // p₁↓} p₂@{p₂↑ // p₂↓} q@{q↑ // q↓}
        (ℚB.≃₀-intro p₁↑p₂↓≃p₂↑p₁↓) =
          begin
            p₁ * q
          ≃⟨⟩
            (p₁↑ // p₁↓) * (q↑ // q↓)
          ≃⟨⟩
            ((p₁↑ * q↑) // (p₁↓ * q↓)) {{AA.nonzero-prodⁱ}}
          ≃⟨ ℚB.≃₀-intro componentEq ⟩
            ((p₂↑ * q↑) // (p₂↓ * q↓)) {{AA.nonzero-prodⁱ}}
          ≃⟨⟩
            (p₂↑ // p₂↓) * (q↑ // q↓)
          ≃⟨⟩
            p₂ * q
          ∎
        where
          componentEq =
            begin
              (p₁↑ * q↑) * (p₂↓ * q↓)
            ≃⟨ AA.transpose ⟩
              (p₁↑ * p₂↓) * (q↑ * q↓)
            ≃⟨ AA.subst₂ p₁↑p₂↓≃p₂↑p₁↓ ⟩
              (p₂↑ * p₁↓) * (q↑ * q↓)
            ≃⟨ AA.transpose ⟩
              (p₂↑ * q↑) * (p₁↓ * q↓)
            ∎

  *-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _*_ _≃_ _≃_
  *-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm {A = ℚ}

  *-substitutive : AA.Substitutive² _*_ _≃_ _≃_
  *-substitutive = AA.substitutive² {A = ℚ}
