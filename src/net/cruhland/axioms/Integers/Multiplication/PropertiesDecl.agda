import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.PropertiesDecl using (Properties)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Multiplication.PropertiesDecl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZP : Properties PA ZB)
  (Z+ : Addition PA ZB ZP)
  (Z- : Negation PA ZB ZP Z+)
  where

open Base ZB using (ℤ)
open import net.cruhland.axioms.Integers.Multiplication.BaseDecl PA ZB ZP Z+ Z-
  using (MultiplicationBase)

record MultiplicationProperties (MB : MultiplicationBase) : Set where
  field
    {{*-absorptive}} : AA.Absorptive² _*_ 0
    {{*-distributive-sub}} : AA.Distributive² _*_ _-_
    {{neg-compatible-+}} : AA.IsCompatible₂ -_ _+_ _+_ _≃_

    neg-mult : {a : ℤ} → -1 * a ≃ - a
    neg-sub-swap : {a b : ℤ} → - (a - b) ≃ b - a
