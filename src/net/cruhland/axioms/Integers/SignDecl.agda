import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.SignDecl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)

record Sign (ZB : Base) (Z+ : Addition ZB) (Z- : Negation ZB Z+) : Set₁ where
  open Base ZB using (ℤ)

  field
    {{positivity}} : Positivity {A = ℤ} 0
    {{negativity}} : Negativity {A = ℤ} 0
    from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)
    neg-Positive : {a : ℤ} → Positive a → Negative (- a)
    neg-Negative : {a : ℤ} → Negative a → Positive (- a)
    trichotomy :
      (a : ℤ) → AA.ExactlyOneOfThree (Negative a) (a ≃ 0) (Positive a)

    fromNatLiteral-preserves-pos :
      ∀ n → Positive {A = ℕ} (fromNatLiteral n) →
      Positive {A = ℤ} (fromNatLiteral n)

    1-Positive : Positive {A = ℤ} 1

-- Confirm that all partial impls typecheck
module _ where
  import net.cruhland.axioms.Integers.SignPartialImpl
