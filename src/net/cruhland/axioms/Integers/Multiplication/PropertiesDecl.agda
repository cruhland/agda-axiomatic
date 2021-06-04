import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.SignDecl using (Sign)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Negative; Positive)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Multiplication.PropertiesDecl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  (ZS : Sign PA ZB Z+ Z-)
  where

open Base ZB using (ℤ)
open import net.cruhland.axioms.Integers.Multiplication.BaseDecl PA ZB Z+ Z-
  using (MultiplicationBase)

record MultiplicationProperties (MB : MultiplicationBase) : Set where
  field
    {{*-absorptive}} : AA.Absorptive² _*_ 0
    {{*-distributive-sub}} : AA.Distributive² _*_ _-_
    {{neg-compatible-+}} : AA.IsCompatible₂ -_ _+_ _+_ _≃_

    neg-mult : {a : ℤ} → -1 * a ≃ - a
    neg-sub-swap : {a b : ℤ} → - (a - b) ≃ b - a
    sub-sign-swap : {a b : ℤ} → Negative (a - b) → Positive (b - a)
