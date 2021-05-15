import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.Sign.BaseDecl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open Base ZB using (ℤ)

record SignBase : Set₁ where
  field
    {{positivity}} : Positivity {A = ℤ} 0
    {{negativity}} : Negativity {A = ℤ} 0
    from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)
    neg-Positive : {a : ℤ} → Positive a → Negative (- a)
    neg-Negative : {a : ℤ} → Negative a → Positive (- a)
    trichotomy :
      (a : ℤ) → AA.ExactlyOneOfThree (Negative a) (a ≃ 0) (Positive a)
