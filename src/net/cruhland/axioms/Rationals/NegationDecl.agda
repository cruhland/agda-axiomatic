import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals.NegationDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open Integers Z using (ℤ)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

record Negation (QB : Base) : Set where
  open Base QB using (ℚ)

  field
    {{dashᴸ}} : Op.Dashᴸ ℚ
    {{neg-substitutive}} : AA.Substitutive₁ {A = ℚ} -_ _≃_ _≃_
    {{neg-compatible-ℤ}} : AA.Compatible₁ {A = ℤ} (_as ℚ) -_ -_ _≃_
