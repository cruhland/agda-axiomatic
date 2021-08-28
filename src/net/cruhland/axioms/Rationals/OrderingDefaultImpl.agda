import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_)
open import net.cruhland.axioms.Ordering as Ord using (_<_; _>_)
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
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using (_∨_; ∨-map; ∨-forceᴸ; ¬_; contrapositive)

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

  order-trichotomy : Ord.Trichotomy ℚ
  order-trichotomy = Ord.trichotomy-intro ord-tri
    where
      ord-tri : (p q : ℚ) → AA.ExactlyOneOfThree (p ≃ q) (p < q) (p > q)
      ord-tri p q = AA.exactlyOneOfThree 1of3 ¬2of3
        where
          sign-tri = S.trichotomy (p - q)

          1of3 : AA.OneOfThree (p ≃ q) (p < q) (p > q)
          1of3 with AA.at-least-one sign-tri
          ... | AA.1st p-q≃0 = AA.1st (ℚ.p≃q-from-p-q≃0 p-q≃0)
          ... | AA.2nd p>q = AA.3rd p>q
          ... | AA.3rd p<q = AA.2nd p<q

          sign-2of3-from-ord-2of3 :
            AA.TwoOfThree (p ≃ q) (p < q) (p > q) →
            AA.TwoOfThree (p - q ≃ 0) (S.Positive (p - q)) (S.Negative (p - q))
          sign-2of3-from-ord-2of3 (AA.1∧2 p≃q neg[p-q]) =
            let p-q≃0 = ℚ.p-q≃0-from-p≃q p≃q
             in AA.1∧3 p-q≃0 neg[p-q]
          sign-2of3-from-ord-2of3 (AA.1∧3 p≃q pos[p-q]) =
            let p-q≃0 = ℚ.p-q≃0-from-p≃q p≃q
             in AA.1∧2 p-q≃0 pos[p-q]
          sign-2of3-from-ord-2of3 (AA.2∧3 neg[p-q] pos[p-q]) =
            AA.2∧3 pos[p-q] neg[p-q]

          ¬2of3 : ¬ AA.TwoOfThree (p ≃ q) (p < q) (p > q)
          ¬2of3 =
            let ¬sign-2of3 = AA.at-most-one sign-tri
             in contrapositive sign-2of3-from-ord-2of3 ¬sign-2of3

  <-transitive : Eq.Transitive _<_
  <-transitive = Eq.transitive <-trans
    where
      <-trans : {p q r : ℚ} → p < q → q < r → p < r
      <-trans {p} {q} {r} neg[p-q] neg[q-r] =
        let neg[[p-q]+[q-r]] = AA.pres neg[p-q] neg[q-r]
            [p-q]+[q-r]≃p-r =
              begin
                (p - q) + (q - r)
              ≃⟨ AA.subst₂ ℚ.sub-defn ⟩
                (p + - q) + (q - r)
              ≃⟨ AA.subst₂ ℚ.sub-defn ⟩
                (p + - q) + (q + - r)
              ≃⟨ AA.[ab][cd]≃a[[bc]d] ⟩
                p + ((- q + q) + - r)
              ≃⟨ AA.subst₂ (AA.subst₂ AA.inv) ⟩
                p + (0 + - r)
              ≃⟨ AA.subst₂ AA.ident ⟩
                p + - r
              ≃˘⟨ ℚ.sub-defn ⟩
                p - r
              ∎
            neg[p-r] = AA.subst₁ [p-q]+[q-r]≃p-r neg[[p-q]+[q-r]]
         in neg[p-r]

  totalOrder : Ord.TotalOrder ℚ
  totalOrder = record { <-from-≤≄ = <₀-from-≤₀≄ }

  <-substitutive-≃ᴸ : AA.Substitutive₂ AA.handᴸ _<_ _≃_ _⟨→⟩_
  <-substitutive-≃ᴸ = AA.substitutive₂ <-subst-≃ᴸ
    where
      <-subst-≃ᴸ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → p₁ < q → p₂ < q
      <-subst-≃ᴸ p₁≃p₂ neg[p₁-r] =
        let neg[p₂-q] = AA.subst₁ (AA.subst₂ p₁≃p₂) neg[p₁-r]
         in neg[p₂-q]

  <-substitutive-≃ᴿ : AA.Substitutive₂ AA.handᴿ _<_ _≃_ _⟨→⟩_
  <-substitutive-≃ᴿ = AA.substitutive₂ <-subst-≃ᴿ
    where
      <-subst-≃ᴿ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → q < p₁ → q < p₂
      <-subst-≃ᴿ p₁≃p₂ neg[q-p₁] =
        let neg[q-p₂] = AA.subst₁ (AA.subst₂ p₁≃p₂) neg[q-p₁]
         in neg[q-p₂]

  <-substitutive-≃ : AA.Substitutive² _<_ _≃_ _⟨→⟩_
  <-substitutive-≃ = AA.substitutive² {A = ℚ}

  <-substitutive-+ᴸ : AA.Substitutive₂ AA.handᴸ _+_ _<_ _<_
  <-substitutive-+ᴸ = AA.substitutive₂ <-subst-+ᴸ
    where
      <-subst-+ᴸ : {p q r : ℚ} → p < q → p + r < q + r
      <-subst-+ᴸ {p} {q} {r} neg[p-q] =
        let p-q≃[p+r]-[q+r] =
              begin
                p - q
              ≃⟨ ℚ.sub-defn ⟩
                p + - q
              ≃˘⟨ AA.subst₂ AA.ident ⟩
                p + (0 + - q)
              ≃˘⟨ AA.subst₂ (AA.subst₂ AA.inv) ⟩
                p + ((r + - r) + - q)
              ≃˘⟨ AA.[ab][cd]≃a[[bc]d] ⟩
                (p + r) + (- r + - q)
              ≃⟨ AA.subst₂ AA.comm ⟩
                (p + r) + (- q + - r)
              ≃˘⟨ AA.subst₂ AA.compat₂ ⟩
                (p + r) + - (q + r)
              ≃˘⟨ ℚ.sub-defn ⟩
                (p + r) - (q + r)
              ∎
         in AA.subst₁ p-q≃[p+r]-[q+r] neg[p-q]

  <-substitutive-+ᴿ : AA.Substitutive₂ AA.handᴿ _+_ _<_ _<_
  <-substitutive-+ᴿ = AA.substᴿ-from-substᴸ-comm₂ {A = ℚ}

  <-substitutive-+ : AA.Substitutive² _+_ _<_ _<_
  <-substitutive-+ = AA.substitutive² {A = ℚ}
