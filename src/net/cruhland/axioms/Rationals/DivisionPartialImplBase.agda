open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op using (_*_; _⁻¹; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Rationals.AdditionDecl using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl using (Base)
open import net.cruhland.axioms.Rationals.MultiplicationDecl
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl using (Reciprocal)
open import net.cruhland.models.Literals

module net.cruhland.axioms.Rationals.DivisionPartialImplBase
  (PA : PeanoArithmetic)
  (Z : Integers PA)
  (QB : Base PA Z)
  (QA : Addition PA Z QB)
  (QN : Negation PA Z QB QA)
  (QM : Multiplication PA Z QB QA QN)
  (QR : Reciprocal PA Z QB QA QN QM)
  where

import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private module ℚ where
  open Base QB public
  open LiteralImpl QB public
  open Multiplication QM public
  open Reciprocal QR public

open ℚ using (ℚ)

instance
  div-ℚ : Op.Slash ℚ (_≄ 0) ℚ
  div-ℚ = Op.division

div-ℚ-defn : {p q : ℚ} {{_ : q ≄ 0}} → p / q ≃ p * q ⁻¹
div-ℚ-defn = Eq.refl
