open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S

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

    positiveDenominator : (q : ℚ) → PositiveDenominator q
