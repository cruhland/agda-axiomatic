import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Negative; Positive)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.MultiplicationDecl
  (PA : PeanoArithmetic) where

open PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

record Multiplication
    (ZB : Base)
    (Z+ : Addition ZB)
    (Z- : Negation ZB Z+)
    (ZS : Sign ZB Z+ Z-)
    : Set where
  open Base ZB using (ℤ)

  field
    {{star}} : Op.Star ℤ
    {{*-substitutive}} : AA.Substitutive² {A = ℤ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℤ} _*_
    {{*-compatible-ℕ}} : AA.Compatible₂ {A = ℕ} (_as ℤ) _*_
    {{*-identity}} : AA.Identity² _*_ 1
    {{*-associative}} : AA.Associative {A = ℤ} _*_

    {{*-distributive}} : AA.Distributive² {A = ℤ} _*_ _+_
    {{*-comm-with-neg}} : AA.FnOpCommutative² -_ _*_

    {{*-absorptive}} : AA.Absorptive² _*_ 0
    {{*-distributive-sub}} : AA.Distributive² _*_ _-_
    {{neg-compatible-+}} : AA.IsCompatible₂ -_ _+_ _+_ _≃_

    neg-mult : {a : ℤ} → -1 * a ≃ - a
    neg-sub-swap : {a b : ℤ} → - (a - b) ≃ b - a
    sub-sign-swap : {a b : ℤ} → Negative (a - b) → Positive (b - a)

-- Confirm that all partial impls typecheck
module _ where
  import net.cruhland.axioms.Integers.MultiplicationPartialImpl
