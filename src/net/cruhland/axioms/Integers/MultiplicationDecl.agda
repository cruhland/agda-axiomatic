import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_*_; Star)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers.MultiplicationDecl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)

record Multiplication (ZB : Base) : Set where
  open Base ZB using (ℤ)

  field
    {{star}} : Star ℤ
    {{*-substitutive}} : AA.Substitutive² {A = ℤ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℤ} _*_
