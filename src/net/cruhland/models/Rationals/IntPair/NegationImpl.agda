import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (⊤)

module net.cruhland.models.Rationals.IntPair.NegationImpl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.models.Rationals.IntPair.BaseDefn PA Z using (QB)

private module ℤ = Integers Z
private module ℚ where
  open import net.cruhland.axioms.Rationals.LiteralImpl PA Z QB public
  open import net.cruhland.models.Rationals.IntPair.AdditionImpl PA Z public
  open import net.cruhland.models.Rationals.IntPair.BaseImpl PA Z public

open ℤ using (ℤ)
open ℚ using (_//_; ℚ)

-₀_ : ℚ → ℚ
-₀ (q↑ // q↓) = (- q↑) // q↓

instance
  dashᴸ : Op.Dashᴸ ℚ
  dashᴸ = Op.dashᴸ -₀_

  neg-substitutive : AA.Substitutive₁ -_ _≃_ _≃_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : {q₁ q₂ : ℚ} → q₁ ≃ q₂ → - q₁ ≃ - q₂
      neg-subst q₁@{q₁↑ // q₁↓} q₂@{q₂↑ // q₂↓} (ℚ.≃₀-intro q₁↑q₂↓≃q₂↑q₁↓) =
          begin
            - q₁
          ≃⟨⟩
            - (q₁↑ // q₁↓)
          ≃⟨⟩
            (- q₁↑) // q₁↓
          ≃⟨ ℚ.≃₀-intro componentEq ⟩
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

  neg-compatible-ℤ : AA.Compatible₁ (_as ℚ) -_ -_ _≃_
  neg-compatible-ℤ = AA.compatible₁ {A = ℤ} neg-compat-ℤ
    where
      neg-compat-ℤ : {a : ℤ} → (- a as ℚ) ≃ - (a as ℚ)
      neg-compat-ℤ {a} =
        begin
          (- a as ℚ)
        ≃⟨⟩
          (- a) // 1
        ≃⟨⟩
          - (a // 1)
        ≃⟨⟩
          - (a as ℚ)
        ∎

  +-inverseᴸ : AA.Inverse AA.handᴸ -_ (const ⊤) _+_ 0
  +-inverseᴸ = AA.inverse +-invᴸ
    where
      +-invᴸ : {q : ℚ} → (- q) + q ≃ 0
      +-invᴸ q@{(q↑ // q↓) {{q↓≄0}}} =
        let instance q↓q↓≄0 = AA.nonzero-prod {{a≄0 = q↓≄0}} {{q↓≄0}}
         in begin
              (- q) + q
            ≃⟨⟩
              - (q↑ // q↓) + (q↑ // q↓)
            ≃⟨⟩
              ((- q↑) // q↓) + (q↑ // q↓)
            ≃⟨⟩
              ((- q↑) * q↓ + q↓ * q↑) // (q↓ * q↓)
            ≃˘⟨ AA.subst₂ (AA.subst₂ AA.fnOpComm) ⟩
              (- (q↑ * q↓) + q↓ * q↑) // (q↓ * q↓)
            ≃⟨ AA.subst₂ (AA.subst₂ AA.comm) ⟩
              (- (q↑ * q↓) + q↑ * q↓) // (q↓ * q↓)
            ≃⟨ AA.subst₂ AA.inv ⟩
              0 // (q↓ * q↓)
            ≃⟨ ℚ.q≃0-from-q↑≃0 Eq.refl ⟩
              0
            ∎

  +-inverseᴿ : AA.Inverse AA.handᴿ -_ (const ⊤) _+_ 0
  +-inverseᴿ = AA.inverseᴿ-from-inverseᴸ {A = ℚ}

  +-inverse : AA.Inverse² -_ (const ⊤) _+_ 0
  +-inverse = AA.inverse² {A = ℚ}
