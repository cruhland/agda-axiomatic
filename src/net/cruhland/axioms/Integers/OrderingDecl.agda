import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (_-_)
open import net.cruhland.axioms.Ordering as Ord using (_≤_; _<_; _>_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Positive)

module net.cruhland.axioms.Integers.OrderingDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

record Ordering
    (ZB : Base)
    (Z+ : Addition ZB)
    (Z- : Negation ZB Z+)
    (ZS : Sign ZB Z+ Z-)
    : Set₁ where
  open Base ZB using (ℤ)

  field
    {{totalOrder}} : Ord.TotalOrder ℤ
    {{≤-antisymmetric}} : AA.Antisymmetric {A = ℤ} _≤_
    <-from-pos : {a b : ℤ} → Positive (b - a) → a < b
    pos-from-< : {a b : ℤ} → a < b → Positive (b - a)
    order-trichotomy : (a b : ℤ) → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
