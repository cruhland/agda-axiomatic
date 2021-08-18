import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.MultiplicationDecl
  (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

private
  module IntegerPredefs
      (ZB : Base)
      (ZA : Addition ZB)
      (ZN : Negation ZB ZA)
      (ZS : Sign ZB ZA ZN)
      where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Negation ZN public
    open Sign ZS public

module MultiplicationPredefs
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZS : Sign ZB ZA ZN)
    where
  private open module ℤ = IntegerPredefs ZB ZA ZN ZS using (ℤ; _≃±1)

  record PosOrNeg (a : ℤ) {{_ : Op.Star ℤ}} : Set where
    constructor PosOrNeg-intro
    field
      {n} : ℕ
      {s} : ℤ
      pos[n] : S.Positive n
      s≃±1 : s ≃±1
      a≃sn : a ≃ s * (n as ℤ)

record Multiplication
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZS : Sign ZB ZA ZN)
    : Set₁ where
  private open module ℤ = IntegerPredefs ZB ZA ZN ZS using (ℤ; _≃±1)
  open MultiplicationPredefs ZB ZA ZN ZS public

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
    {{*-cancellative}} : AA.Cancellative² {A = ℤ} _*_ _≃_ _≃_ (_≄ 0)

    {{*-preserves-≃±1}} : AA.Preserves _≃±1 _*_
    {{*-preserves-Positive}} : AA.Preserves {A = ℤ} S.Positive _*_
    PosOrNeg-from-nonzero : {a : ℤ} → a ≄ 0 → PosOrNeg a
    nonzero-from-PosOrNeg : {a : ℤ} → PosOrNeg a → a ≄ 0
    *-neither-zero : {a b : ℤ} → a ≄ 0 → b ≄ 0 → a * b ≄ 0
    {{zero-product}} : AA.ZeroProduct {A = ℤ} _*_

    {{*-distributive-sub}} : AA.Distributive² (AA.tc₂ _*_) _-_
    {{neg-compatible-+}} : AA.Compatible₂ {A = ℤ} (AA.tc₁ λ a → - a) _+_ _+_ _≃_

    neg-mult : {a : ℤ} → -1 * a ≃ - a
    neg-sub-swap : {a b : ℤ} → - (a - b) ≃ b - a
    sub-sign-swap : {a b : ℤ} → S.Negative (a - b) → S.Positive (b - a)
