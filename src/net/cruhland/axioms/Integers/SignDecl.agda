import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq using (_≃_; Eq)
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity)
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.SignDecl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)

module SignPredefs (ZB : Base) (Z+ : Addition ZB) (Z- : Negation ZB Z+) where
  open Base ZB using (ℤ)

  infix 4 _≃±1
  data _≃±1 (s : ℤ) : Set where
    ≃+1-intro : s ≃ 1 → s ≃±1
    ≃-1-intro : s ≃ -1 → s ≃±1

  record _≃_[posℕ] (a : ℤ) (f : ℤ → ℤ) : Set where
    constructor ≃posℕ-intro
    field
      {n} : ℕ
      pos[n] : Positive n
      a≃n : a ≃ f (n as ℤ)

record Sign (ZB : Base) (Z+ : Addition ZB) (Z- : Negation ZB Z+) : Set₁ where
  open Base ZB using (ℤ)
  open SignPredefs ZB Z+ Z- public

  field
    {{positivity}} : Positivity {A = ℤ} 0
    {{negativity}} : Negativity {A = ℤ} 0

    {{≃±1-substitutive}} : AA.Substitutive₁ _≃±1 _≃_ _⟨→⟩_
    ≃±1-absorbs-neg : {a : ℤ} → - a ≃±1 → a ≃±1

    posℕ-from-posℤ : {a : ℤ} → Positive a → a ≃ id [posℕ]
    posℕ-from-negℤ : {a : ℤ} → Negative a → a ≃ -_ [posℕ]
    posℤ-from-posℕ : {a : ℤ} → a ≃ id [posℕ] → Positive a
    negℤ-from-posℕ : {a : ℤ} → a ≃ -_ [posℕ] → Negative a

    from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)
    +-preserves-pos : AA.Preserves {A = ℤ} Positive _+_
    neg-Positive : {a : ℤ} → Positive a → Negative (- a)
    neg-Negative : {a : ℤ} → Negative a → Positive (- a)
    trichotomy :
      (a : ℤ) → AA.ExactlyOneOfThree (Negative a) (a ≃ 0) (Positive a)

    fromNatLiteral-preserves-pos :
      ∀ n → Positive {A = ℕ} (fromNatLiteral n) →
      Positive {A = ℤ} (fromNatLiteral n)

    1-Positive : Positive {A = ℤ} 1
