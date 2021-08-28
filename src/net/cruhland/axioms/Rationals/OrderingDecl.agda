import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_+_; _*_)
open import net.cruhland.axioms.Ordering as Ord using (_<_; _>_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_)

module net.cruhland.axioms.Rationals.OrderingDecl
  (PA : PeanoArithmetic) (Z : Integers PA) where

open import net.cruhland.axioms.Rationals.AdditionDecl PA Z using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl PA Z using (Base)
open import net.cruhland.axioms.Rationals.DivisionDecl PA Z using (Division)
import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
open import net.cruhland.axioms.Rationals.MultiplicationDecl PA Z
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl PA Z using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl PA Z using (Reciprocal)
open import net.cruhland.axioms.Rationals.SignDecl PA Z using (Sign)

private
  module RationalPredefs
      (QB : Base)
      (QA : Addition QB)
      (QN : Negation QB QA)
      (QM : Multiplication QB QA QN)
      (QR : Reciprocal QB QA QN QM)
      (QD : Division QB QA QN QM QR)
      (QS : Sign QB QA QN QM QR QD)
      where
    open Addition QA public
    open Base QB public
    open Division QD public
    open LiteralImpl QB public
    open Multiplication QM public
    open Negation QN public
    open Reciprocal QR public
    open Sign QS public

record Ordering
    (QB : Base)
    (QA : Addition QB)
    (QN : Negation QB QA)
    (QM : Multiplication QB QA QN)
    (QR : Reciprocal QB QA QN QM)
    (QD : Division QB QA QN QM QR)
    (QS : Sign QB QA QN QM QR QD)
    : Set₁ where
  private
    open module ℚ = RationalPredefs QB QA QN QM QR QD QS using (ℚ)

  field
    {{totalOrder}} : Ord.TotalOrder ℚ
    {{<-substitutive-≃}} : AA.Substitutive² {A = ℚ} _<_ _≃_ _⟨→⟩_
    {{>-substitutive-≃}} : AA.Substitutive² {A = ℚ} _>_ _≃_ _⟨→⟩_
    {{<-substitutive-+}} : AA.Substitutive² {A = ℚ} _+_ _<_ _<_
    {{<-substitutive-*-pos}} : AA.Substitutive²ᶜ (AA.tc₂ _*_) _<_ _<_ S.Positive
    {{<-substitutive-*-neg}} : AA.Substitutive²ᶜ (AA.tc₂ _*_) _<_ _>_ S.Negative
