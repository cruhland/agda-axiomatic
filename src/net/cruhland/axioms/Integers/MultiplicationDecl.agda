import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.MultiplicationDecl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)

private
  open module ℕ = PeanoArithmetic PA using (ℕ)
  module IntegerPredefs
      (ZB : Base) (ZA : Addition ZB) (ZN : Negation ZB ZA) where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Negation ZN public

record Multiplication
    (ZB : Base) (ZA : Addition ZB) (ZN : Negation ZB ZA) : Set₁ where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN using (ℤ)

  field
    {{star}} : Op.Star ℤ
    {{*-substitutive}} : AA.Substitutive² {A = ℤ} _*_ _≃_ _≃_
    {{*-commutative}} : AA.Commutative {A = ℤ} _*_
    {{*-compatible-ℕ}} : AA.Compatible₂ {A = ℕ} (AA.tc₁ (_as ℤ)) _*_ _*_ _≃_
    {{*-identity}} : AA.Identity² {A = ℤ} _*_ 1
    {{*-associative}} : AA.Associative {A = ℤ} _*_
    {{*-distributive}} : AA.Distributive² {A = ℤ} (AA.tc₂ _*_) _+_
    {{*-comm-with-neg}} : AA.FnOpCommutative² -_ -_ (AA.tc₂ _*_)
    {{*-absorptive}} : AA.Absorptive² {A = ℤ} (AA.tc₂ _*_)

    {{*-distributive-sub}} : AA.Distributive² (AA.tc₂ _*_) _-_
    {{neg-compatible-+}} : AA.Compatible₂ {A = ℤ} (AA.tc₁ λ a → - a) _+_ _+_ _≃_

    neg-mult : {a : ℤ} → -1 * a ≃ - a
    neg-sub-swap : {a b : ℤ} → - (a - b) ≃ b - a
