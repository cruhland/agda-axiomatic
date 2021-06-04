import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Operators using (_+_; -_; _*_; Star)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Multiplication.BaseDecl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  where

open PeanoArithmetic PA using (ℕ)
open Base ZB using (ℤ)

record MultiplicationBase : Set where
  field
    {{star}} : Star ℤ
    {{*-substitutive}} : AA.Substitutive² {A = ℤ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℤ} _*_
    {{*-compatible-ℕ}} : AA.Compatible₂ {A = ℕ} (_as ℤ) _*_
    {{*-identity}} : AA.Identity² _*_ 1
    {{*-associative}} : AA.Associative {A = ℤ} _*_

    {{*-distributive}} : AA.Distributive² {A = ℤ} _*_ _+_
    {{*-comm-with-neg}} : AA.FnOpCommutative² -_ _*_
