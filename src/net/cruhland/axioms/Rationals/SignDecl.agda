import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_value_)
open import net.cruhland.axioms.Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (-_; _*_; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_)

module net.cruhland.axioms.Rationals.SignDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
open import net.cruhland.axioms.Rationals.DivisionDecl PA Z using (Division)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)

private
  open module ℤ = Integers Z using (ℤ)
  module RationalPredefs
      (QB : Base)
      (QA : Addition QB)
      (QN : Negation QB QA)
      (QM : Multiplication QB QA QN)
      (QR : Reciprocal QB QA QN QM)
      (QD : Division QB QA QN QM QR)
      where
    open Addition QA public
    open Base QB public
    open Division QD public
    open LiteralImpl QB public
    open Multiplication QM public
    open Negation QN public
    open Reciprocal QR public

module SignPredefs
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    (QR : Reciprocal QB QA QN QM)
    (QD : Division QB QA QN QM QR)
    where
  private
    open module ℚ = RationalPredefs QB QA QN QM QR QD using (ℚ)

  record PositiveDenominator (q : ℚ) : Set where
    constructor positiveDenominator-intro
    field
      {a b} : ℤ
      pos[b] : S.Positive b
      q≃a/b : let instance b≄0 = S.pos≄0 pos[b] in q ≃ a / b

record Sign
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    (QR : Reciprocal QB QA QN QM)
    (QD : Division QB QA QN QM QR)
    : Set₁ where
  private
    open module ℚ = RationalPredefs QB QA QN QM QR QD using (ℚ)
  open SignPredefs QB QA QN QM QR QD public

  field
    {{positivity}} : S.Positivity ℚ
    {{negativity}} : S.Negativity ℚ
    {{sign-common}} : S.SignCommon ℚ
    {{*-preserves-pos}} : AA.Preserves {A = ℚ} S.Positive _*_

    positiveDenominator : (q : ℚ) → PositiveDenominator q
    neg*pos≃neg : {p q : ℚ} → S.Negative p → S.Positive q → S.Negative (p * q)
    neg*neg≃pos : {p q : ℚ} → S.Negative p → S.Negative q → S.Positive (p * q)
    [-1]≄1 : -1 ≄ (ℚ value 1)
    q≃0-from-q≃[-q] : {q : ℚ} → q ≃ - q → q ≃ 0

    sgn : ℚ → ℚ
    sgn[q]≃0-from-q≃0 : {q : ℚ} → q ≃ 0 → sgn q ≃ 0
    q≃0-from-sgn[q]≃0 : {q : ℚ} → sgn q ≃ 0 → q ≃ 0
    sgn[q]≃1-from-pos[q] : {q : ℚ} → S.Positive q → sgn q ≃ 1
    pos[q]-from-sgn[q]≃1 : {q : ℚ} → sgn q ≃ 1 → S.Positive q
    sgn[q]≃[-1]-from-neg[q] : {q : ℚ} → S.Negative q → sgn q ≃ -1
    neg[q]-from-sgn[q]≃[-1] : {q : ℚ} → sgn q ≃ -1 → S.Negative q
    {{sgn-substitutive}} : AA.Substitutive₁ sgn _≃_ _≃_

    abs : ℚ → ℚ
    abs[q]≃0-from-q≃0 : {q : ℚ} → q ≃ 0 → abs q ≃ 0
    q≃0-from-abs[q]≃0 : {q : ℚ} → abs q ≃ 0 → q ≃ 0
    abs[q]≃q-from-pos[q] : {q : ℚ} → S.Positive q → abs q ≃ q
    ¬neg[q]-from-abs[q]≃q : {q : ℚ} → abs q ≃ q → ¬ S.Negative q
    abs[q]≃[-q]-from-neg[q] : {q : ℚ} → S.Negative q → abs q ≃ - q
    ¬pos[q]-from-abs[q]≃[-q] : {q : ℚ} → abs q ≃ - q → ¬ S.Positive q
    {{abs-substitutive}} : AA.Substitutive₁ abs _≃_ _≃_

    dist : ℚ → ℚ → ℚ
