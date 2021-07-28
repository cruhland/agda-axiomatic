import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_⁻¹)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.ReciprocalDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

record Reciprocal (QB : Base) : Set where
  open Base QB using (ℚ)

  field
    {{reciprocal}} : Op.SupNegOne ℚ (_≄ 0)
    {{recip-substitutive}} : AA.Substitutive₁ᶜ {A = ℚ} _⁻¹ _≃_ _≃_
