import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Operators using (_-_)
open import net.cruhland.axioms.Ordering as Ord using (_≤_; _<_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S

module net.cruhland.axioms.Integers.OrderingDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

private
  module IntegerPredefs
      (ZB : Base)
      (ZA : Addition ZB)
      (ZN : Negation ZB ZA)
      (ZM : Multiplication ZB ZA ZN)
      (ZS : Sign ZB ZA ZN ZM)
      where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Multiplication ZM public
    open Negation ZN public
    open Sign ZS public

record Ordering
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZM : Multiplication ZB ZA ZN)
    (ZS : Sign ZB ZA ZN ZM)
    : Set₁ where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN ZM ZS using (ℤ)

  field
    {{totalOrder}} : Ord.TotalOrder ℤ
    {{≤-antisymmetric}} : AA.Antisymmetric {A = ℤ} _≤_
    <-from-pos : {a b : ℤ} → S.Positive (b - a) → a < b
    pos-from-< : {a b : ℤ} → a < b → S.Positive (b - a)
