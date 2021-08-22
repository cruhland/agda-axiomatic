import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq using (_≃_; Eq)
open import net.cruhland.axioms.Operators using (-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.SignDecl (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)

private
  module IntegerPredefs
      (ZB : Base) (ZA : Addition ZB) (ZN : Negation ZB ZA) where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Negation ZN public

module SignPredefs (ZB : Base) (ZA : Addition ZB) (ZN : Negation ZB ZA) where
  private open module ℤ = IntegerPredefs ZB ZA ZN using (ℤ)

  infix 4 _≃±1
  data _≃±1 (s : ℤ) : Set where
    ≃+1-intro : s ≃ 1 → s ≃±1
    ≃-1-intro : s ≃ -1 → s ≃±1

  record _≃_[posℕ] (a : ℤ) (f : ℤ → ℤ) : Set where
    constructor ≃posℕ-intro
    field
      {n} : ℕ
      pos[n] : S.Positive n
      a≃n : a ≃ f (n as ℤ)

record Sign (ZB : Base) (ZA : Addition ZB) (ZN : Negation ZB ZA) : Set₁ where
  private open module ℤ = IntegerPredefs ZB ZA ZN using (ℤ)
  open SignPredefs ZB ZA ZN public

  field
    {{positivity}} : S.Positivity ℤ
    {{negativity}} : S.Negativity ℤ
    {{sign-common}} : S.SignCommon ℤ

    {{≃±1-substitutive}} : AA.Substitutive₁ _≃±1 _≃_ _⟨→⟩_
    ≃±1-absorbs-neg : {a : ℤ} → - a ≃±1 → a ≃±1

    posℕ-from-posℤ : {a : ℤ} → S.Positive a → a ≃ id [posℕ]
    posℕ-from-negℤ : {a : ℤ} → S.Negative a → a ≃ -_ [posℕ]
    posℤ-from-posℕ : {a : ℤ} → a ≃ id [posℕ] → S.Positive a
    negℤ-from-posℕ : {a : ℤ} → a ≃ -_ [posℕ] → S.Negative a

    from-ℕ-preserves-pos : {n : ℕ} → S.Positive n → S.Positive (n as ℤ)
    1-Positive : S.Positive {A = ℤ} 1
