import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_As_; _as_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.axioms.Operators as Op using (-_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Integers.SignDecl (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)

private
  open module ℕ = PeanoArithmetic PA using (ℕ)
  module IntegerPredefs
      (ZB : Base)
      (ZA : Addition ZB)
      (ZN : Negation ZB ZA)
      (ZM : Multiplication ZB ZA ZN)
      where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Multiplication ZM public
    open Negation ZN public

module SignPredefs
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZM : Multiplication ZB ZA ZN)
    where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN ZM using (ℤ)

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

  record PosOrNeg (a : ℤ) : Set where
    constructor PosOrNeg-intro
    field
      {n} : ℕ
      {s} : ℤ
      pos[n] : S.Positive n
      s≃±1 : s ≃±1
      a≃sn : a ≃ s * (n as ℤ)

record Sign
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZM : Multiplication ZB ZA ZN)
    : Set₁ where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN ZM using (ℤ)
  open SignPredefs ZB ZA ZN ZM public

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

    {{*-preserves-≃±1}} : AA.Preserves _≃±1 _*_
    {{*-preserves-Positive}} : AA.Preserves {A = ℤ} S.Positive _*_
    PosOrNeg-from-nonzero : {a : ℤ} → a ≄ 0 → PosOrNeg a
    nonzero-from-PosOrNeg : {a : ℤ} → PosOrNeg a → a ≄ 0
    *-neither-zero : {a b : ℤ} → a ≄ 0 → b ≄ 0 → a * b ≄ 0
    {{zero-product}} : AA.ZeroProduct {A = ℤ} _*_
    {{*-cancellative}} : AA.Cancellative² {A = ℤ} _*_ _≃_ _≃_ (_≄ 0)
    sub-sign-swap : {a b : ℤ} → S.Negative (a - b) → S.Positive (b - a)
