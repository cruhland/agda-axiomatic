import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_-_)
import net.cruhland.axioms.Ordering as Ord
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Rationals.AdditionDecl using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl using (Base)
open import net.cruhland.axioms.Rationals.DivisionDecl using (Division)
open import net.cruhland.axioms.Rationals.MultiplicationDecl
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl using (Reciprocal)
open import net.cruhland.axioms.Rationals.SignDecl using (Sign)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Logic using (_∨_; ∨-map; ∨-forceᴸ)

module net.cruhland.axioms.Rationals.OrderingDefaultImpl
  (PA : PeanoArithmetic)
  (Z : Integers PA)
  (QB : Base PA Z)
  (QA : Addition PA Z QB)
  (QN : Negation PA Z QB QA)
  (QM : Multiplication PA Z QB QA QN)
  (QR : Reciprocal PA Z QB QA QN QM)
  (QD : Division PA Z QB QA QN QM QR)
  (QS : Sign PA Z QB QA QN QM QR QD)
  where

import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl

private
  module ℚ where
    open Addition QA public
    open Base QB public
    open Division QD public
    open LiteralImpl QB public
    open Multiplication QM public
    open Negation QN public
    open Reciprocal QR public
    open Sign QS public

open ℚ using (ℚ)

_>₀_ : ℚ → ℚ → Set
p >₀ q = S.Positive (p - q)

_<₀_ : ℚ → ℚ → Set
p <₀ q = S.Negative (p - q)

>₀-flip : {p q : ℚ} → p >₀ q → q <₀ p
>₀-flip {p} {q} pos[p-q] =
  let neg[-[p-q]] = S.neg-Positive pos[p-q]
      -[p-q]≃q-p = ℚ.neg-sub
   in AA.subst₁ -[p-q]≃q-p neg[-[p-q]]

<₀-flip : {p q : ℚ} → p <₀ q → q >₀ p
<₀-flip neg[p-q] =
  let pos[-[p-q]] = S.neg-Negative neg[p-q]
      -[p-q]≃q-p = ℚ.neg-sub
   in AA.subst₁ -[p-q]≃q-p pos[-[p-q]]

≤₀-flip : {p q : ℚ} → p <₀ q ∨ p ≃ q → q >₀ p ∨ q ≃ p
≤₀-flip = ∨-map <₀-flip Eq.sym

≥₀-flip : {p q : ℚ} → p >₀ q ∨ p ≃ q → q <₀ p ∨ q ≃ p
≥₀-flip = ∨-map >₀-flip Eq.sym

<₀-from-≤₀≄ : {p q : ℚ} → p <₀ q ∨ p ≃ q → p ≄ q → p <₀ q
<₀-from-≤₀≄ p<₀q∨p≃q p≄q = ∨-forceᴸ p≄q p<₀q∨p≃q

instance
  greaterThan : Ord.GreaterThan ℚ
  greaterThan = Ord.greaterThan _>₀_

  lessThan : Ord.LessThan ℚ
  lessThan = Ord.lessThan _<₀_

  strictOrder : Ord.StrictOrder ℚ
  strictOrder = record { <-flip = <₀-flip ; >-flip = >₀-flip }

  greaterThanOrEqual : Ord.GreaterThanOrEqual ℚ
  greaterThanOrEqual = Ord.gte-from-eq-gt

  lessThanOrEqual : Ord.LessThanOrEqual ℚ
  lessThanOrEqual = Ord.lte-from-eq-lt

  nonStrictOrder : Ord.NonStrictOrder ℚ
  nonStrictOrder = record { ≤-flip = ≤₀-flip ; ≥-flip = ≥₀-flip }

  totalOrder : Ord.TotalOrder ℚ
  totalOrder = record { <-from-≤≄ = <₀-from-≤₀≄ }
