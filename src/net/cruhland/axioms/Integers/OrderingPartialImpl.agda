import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Ordering as Ord using (_≤_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Function
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (∧-intro)

module net.cruhland.axioms.Integers.OrderingPartialImpl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  where

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤB = Base ZB using (ℤ)

record _≤₀_ (a b : ℤ) : Set where
  constructor ≤₀-intro
  field
    {d} : ℕ
    a+d≃b : a + (d as ℤ) ≃ b

record _<₀_ (a b : ℤ) : Set where
  constructor <₀-intro
  field
    a≤b : a ≤₀ b
    a≄b : a ≄ b

instance
  lessThanOrEqual : Ord.LessThanOrEqual ℤ
  lessThanOrEqual = Ord.lessThanOrEqual _≤₀_

  lessThan : Ord.LessThan ℤ
  lessThan = Ord.lessThan _<₀_

  ≤-antisymmetric : AA.Antisymmetric _≤_
  ≤-antisymmetric = AA.antisymmetric ≤-antisym
    where
      ≤-antisym : {a b : ℤ} → a ≤ b → b ≤ a → a ≃ b
      ≤-antisym {a} {b} (≤₀-intro {d₁} a+d₁≃b) (≤₀-intro {d₂} b+d₂≃a) =
        let d₁+d₂-as-ℤ≃0-as-ℤ =
              begin
                (d₁ + d₂ as ℤ)
              ≃⟨ AA.compat₂ ⟩
                (d₁ as ℤ) + (d₂ as ℤ)
              ≃˘⟨ AA.ident ⟩
                0 + ((d₁ as ℤ) + (d₂ as ℤ))
              ≃˘⟨ AA.subst₂ AA.inv ⟩
                ((- a) + a) + ((d₁ as ℤ) + (d₂ as ℤ))
              ≃⟨ AA.assoc ⟩
                (- a) + (a + ((d₁ as ℤ) + (d₂ as ℤ)))
              ≃˘⟨ AA.subst₂ AA.assoc ⟩
                (- a) + ((a + (d₁ as ℤ)) + (d₂ as ℤ))
              ≃⟨ AA.subst₂ (AA.subst₂ a+d₁≃b) ⟩
                (- a) + (b + (d₂ as ℤ))
              ≃⟨ AA.subst₂ b+d₂≃a ⟩
                (- a) + a
              ≃⟨ AA.inv ⟩
                0
              ≃⟨ ℤB.fromNatLiteral≃casts 0 ⟩
                (0 as ℤ)
              ∎
            ∧-intro _ d₂≃0 = ℕ.+-both-zero (AA.inject d₁+d₂-as-ℤ≃0-as-ℤ)
         in begin
              a
            ≃˘⟨ b+d₂≃a ⟩
              b + (d₂ as ℤ)
            ≃⟨ AA.subst₂ (AA.subst₁ d₂≃0) ⟩
              b + (0 as ℤ)
            ≃˘⟨ AA.subst₂ (ℤB.fromNatLiteral≃casts 0) ⟩
              b + 0
            ≃⟨ AA.ident ⟩
              b
            ∎