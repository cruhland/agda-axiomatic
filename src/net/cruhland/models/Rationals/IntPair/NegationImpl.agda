import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Rationals.IntPair.NegationImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z as ℚB
  using (_//_; ℚ)

-₀_ : ℚ → ℚ
-₀ (q↑ // q↓) = (- q↑) // q↓

instance
  dashᴸ : Op.Dashᴸ ℚ
  dashᴸ = Op.dashᴸ -₀_

  neg-substitutive : AA.Substitutive₁ -_ _≃_ _≃_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : {q₁ q₂ : ℚ} → q₁ ≃ q₂ → - q₁ ≃ - q₂
      neg-subst q₁@{q₁↑ // q₁↓} q₂@{q₂↑ // q₂↓} (ℚB.≃₀-intro q₁↑q₂↓≃q₂↑q₁↓) =
          begin
            - q₁
          ≃⟨⟩
            - (q₁↑ // q₁↓)
          ≃⟨⟩
            (- q₁↑) // q₁↓
          ≃⟨ ℚB.≃₀-intro componentEq ⟩
            (- q₂↑ ) // q₂↓
          ≃⟨⟩
            - (q₂↑ // q₂↓)
          ≃⟨⟩
            - q₂
          ∎
        where
          componentEq =
            begin
              (- q₁↑) * q₂↓
            ≃˘⟨ AA.fnOpComm ⟩
              - (q₁↑ * q₂↓)
            ≃⟨ AA.subst₁ q₁↑q₂↓≃q₂↑q₁↓ ⟩
              - (q₂↑ * q₁↓)
            ≃⟨ AA.fnOpComm ⟩
              (- q₂↑) * q₁↓
            ∎
