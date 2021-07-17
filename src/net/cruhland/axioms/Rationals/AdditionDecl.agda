import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_+_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Rationals.AdditionDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open Integers Z using (ℤ)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)

record Addition (QB : Base) : Set where
  open Base QB using (ℚ)

  field
    {{plus}} : Op.Plus ℚ
    {{+-substitutive}} : AA.Substitutive² {A = ℚ} _+_ _≃_ _≃_
    {{+-commutative}} : AA.Commutative {A = ℚ} _+_
    {{+-associative}} : AA.Associative {A = ℚ} _+_
    {{+-compatible-ℤ}} : AA.Compatible₂ {A = ℤ} (_as ℚ) _+_ _+_ _≃_
