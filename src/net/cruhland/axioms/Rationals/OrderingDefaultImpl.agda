import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators as Op
  using (_+_; -_; _-_; _*_; _≤_; _≥_; _<_; _>_)
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
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using ( _∨_; ∨-introᴸ; ∨-introᴿ; ∨-map; ∨-forceᴸ
        ; _↯_; ¬_; ¬-intro; contrapositive)

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

with->₀-flipped :
  {p₁ p₂ q₁ q₂ : ℚ} → (p₁ <₀ q₁ → p₂ <₀ q₂) → q₁ >₀ p₁ → q₂ >₀ p₂
with->₀-flipped f q₁>₀p₁ =
  let p₁<₀q₁ = >₀-flip q₁>₀p₁
      p₂<₀q₂ = f p₁<₀q₁
      q₂>₀p₂ = <₀-flip p₂<₀q₂
   in q₂>₀p₂

instance
  lt : Op.Lt ℚ
  lt = Op.lt _<₀_

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

  <-irreflexive : AA.Irreflexive _<_
  <-irreflexive = AA.irreflexive <-irrefl
    where
      <-irrefl : {q : ℚ} → ¬ S.Negative (q - q)
      <-irrefl = ¬-intro λ neg[q-q] →
        let q-q≃0 = ℚ.sub-same
            q-q≄0 = S.neg≄0 neg[q-q]
         in q-q≃0 ↯ q-q≄0

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

  lessThan : Ord.Strict _<_
  lessThan = Ord.strict-intro {A = ℚ}

  gt : Op.Gt ℚ
  gt = Op.gt _>₀_

  >-substitutive-≃ᴸ : AA.Substitutive₂ AA.handᴸ _>_ _≃_ _⟨→⟩_
  >-substitutive-≃ᴸ = AA.substitutive₂ >-subst-≃ᴸ
    where
      >-subst-≃ᴸ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → p₁ > q → p₂ > q
      >-subst-≃ᴸ p₁≃p₂ p₁>q = with->₀-flipped (AA.subst₂ p₁≃p₂) p₁>q

  >-substitutive-≃ᴿ : AA.Substitutive₂ AA.handᴿ _>_ _≃_ _⟨→⟩_
  >-substitutive-≃ᴿ = AA.substitutive₂ >-subst-≃ᴿ
    where
      >-subst-≃ᴿ : {p₁ p₂ q : ℚ} → p₁ ≃ p₂ → q > p₁ → q > p₂
      >-subst-≃ᴿ p₁≃p₂ q>p₁ = with->₀-flipped (AA.subst₂ p₁≃p₂) q>p₁

  >-substitutive-≃ : AA.Substitutive² {A = ℚ} _>_ _≃_ _⟨→⟩_
  >-substitutive-≃ = AA.substitutive² {A = ℚ}

  >-irreflexive : AA.Irreflexive _>_
  >-irreflexive = AA.irreflexive >-irrefl
    where
      >-irrefl : {q : ℚ} → ¬ S.Positive (q - q)
      >-irrefl = ¬-intro λ pos[q-q] →
        let q-q≃0 = ℚ.sub-same
            q-q≄0 = S.pos≄0 pos[q-q]
         in q-q≃0 ↯ q-q≄0

  >-transitive : Eq.Transitive _>_
  >-transitive = Eq.transitive >-trans
    where
      >-trans : {p q r : ℚ} → p > q → q > r → p > r
      >-trans p>q q>r = <₀-flip (Eq.trans (>₀-flip q>r) (>₀-flip p>q))

  greaterThan : Ord.Strict _>_
  greaterThan = Ord.strict-intro {A = ℚ}

  strictOrder : Ord.Strict² _<_ _>_
  strictOrder = record { lt-flip = <₀-flip ; gt-flip = >₀-flip }

  gtEq : Op.GtEq ℚ
  gtEq = Ord.gtEq-⋚ _>_

  greaterThanOrEqual : Ord.NonStrict _≥_
  greaterThanOrEqual = Ord.nonstrict-from-strict

  ltEq : Op.LtEq ℚ
  ltEq = Ord.ltEq-⋚ _<_

  lessThanOrEqual : Ord.NonStrict _≤_
  lessThanOrEqual = Ord.nonstrict-from-strict

  nonStrictOrder : Ord.NonStrict² _≤_ _≥_
  nonStrictOrder = record { lte-flip = ≤₀-flip ; gte-flip = ≥₀-flip }

  -- Instances needed in impls only
  ≤-substitutive-≃ : AA.Substitutive² _≤_ _≃_ _⟨→⟩_
  ≤-substitutive-≃ = Ord.NonStrict.substitutive lessThanOrEqual

  order-trichotomy : Ord.Trichotomy _<_ _>_
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

  totalOrder : Ord.TotalOrder _≤_ _≥_ _<_ _>_
  totalOrder = record { lt-from-lte-≄ = <₀-from-≤₀≄ }

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

  <-substitutive-*-posᴸ :
    AA.Substitutive₂ᶜ AA.handᴸ (AA.tc₂ _*_) _<_ _<_ S.Positive
  <-substitutive-*-posᴸ = AA.substitutive₂ <-subst-*-posᴸ
    where
      <-subst-*-posᴸ : {p q r : ℚ} {{_ : S.Positive r}} → p < q → p * r < q * r
      <-subst-*-posᴸ {{pos[r]}} neg[p-q] =
        let neg[[p-q]r] = ℚ.neg*pos≃neg neg[p-q] pos[r]
            neg[pr-qr] = AA.subst₁ AA.distrib neg[[p-q]r]
         in neg[pr-qr]

  <-substitutive-*-posᴿ :
    AA.Substitutive₂ᶜ AA.handᴿ (AA.tc₂ _*_) _<_ _<_ S.Positive
  <-substitutive-*-posᴿ = AA.substᴿ-from-substᴸ-comm₂

  <-substitutive-*-pos : AA.Substitutive²ᶜ (AA.tc₂ _*_) _<_ _<_ S.Positive
  <-substitutive-*-pos = AA.substitutive²

  <-substitutive-*-negᴸ :
    AA.Substitutive₂ᶜ AA.handᴸ (AA.tc₂ _*_) _<_ _>_ S.Negative
  <-substitutive-*-negᴸ = AA.substitutive₂ <-subst-*-negᴸ
    where
      <-subst-*-negᴸ : {p q r : ℚ} {{_ : S.Negative r}} → p < q → p * r > q * r
      <-subst-*-negᴸ {{neg[r]}} neg[p-q] =
        let pos[[p-q]r] = ℚ.neg*neg≃pos neg[p-q] neg[r]
            pos[pr-qr] = AA.subst₁ AA.distrib pos[[p-q]r]
         in pos[pr-qr]

  <-substitutive-*-negᴿ :
    AA.Substitutive₂ᶜ AA.handᴿ (AA.tc₂ _*_) _<_ _>_ S.Negative
  <-substitutive-*-negᴿ = AA.substᴿ-from-substᴸ-comm₂

  <-substitutive-*-neg : AA.Substitutive²ᶜ (AA.tc₂ _*_) _<_ _>_ S.Negative
  <-substitutive-*-neg = AA.substitutive²

  ≤-substitutive-+ᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≤_ _≤_
  ≤-substitutive-+ᴸ = AA.substitutive₂ ≤-subst-+ᴸ
    where
      ≤-subst-+ᴸ : {p q r : ℚ} → p ≤ q → p + r ≤ q + r
      ≤-subst-+ᴸ (∨-introᴸ p<q) = ∨-introᴸ (AA.subst₂ p<q)
      ≤-subst-+ᴸ (∨-introᴿ p≃q) = ∨-introᴿ (AA.subst₂ p≃q)

  ≤-substitutive-+ᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≤_ _≤_
  ≤-substitutive-+ᴿ = AA.substᴿ-from-substᴸ-comm₂ {A = ℚ}

  ≤-substitutive-+ : AA.Substitutive² _+_ _≤_ _≤_
  ≤-substitutive-+ = AA.substitutive² {A = ℚ}

pos-from->0 : {q : ℚ} → q > 0 → S.Positive q
pos-from->0 pos[q-0] = AA.subst₁ AA.ident pos[q-0]

neg-from-<0 : {q : ℚ} → q < 0 → S.Negative q
neg-from-<0 neg[q-0] = AA.subst₁ AA.ident neg[q-0]

abs≥0 : {q : ℚ} → ℚ.abs q ≥ 0
abs≥0 {q} with AA.at-least-one (Ord.trichotomy q 0)
... | AA.1st q≃0 =
  let abs[q]≃0 = ℚ.abs[q]≃0-from-q≃0 q≃0
   in ∨-introᴿ abs[q]≃0
... | AA.2nd neg[q-0] =
  let neg[q] = AA.subst₁ AA.ident neg[q-0]
      abs[q]≃-q = ℚ.abs[q]≃[-q]-from-neg[q] neg[q]
      pos[-q] = S.neg-Negative neg[q]
      pos[abs[q]] = AA.subst₁ (Eq.sym abs[q]≃-q) pos[-q]
      pos[abs[q]-0] = AA.subst₁ (Eq.sym AA.ident) pos[abs[q]]
   in ∨-introᴸ pos[abs[q]-0]
... | AA.3rd pos[q-0] =
  let pos[q] = AA.subst₁ AA.ident pos[q-0]
      abs[q]≃q = ℚ.abs[q]≃q-from-pos[q] pos[q]
      pos[abs[q]] = AA.subst₁ (Eq.sym abs[q]≃q) pos[q]
      pos[abs[q]-0] = AA.subst₁ (Eq.sym AA.ident) pos[abs[q]]
   in ∨-introᴸ pos[abs[q]-0]

*-sgn-max : {q s : ℚ} {{_ : ℚ.Sgn s}} → q * s ≤ q * ℚ.sgn q
*-sgn-max {q} {{Sgn[s]}} with AA.at-least-one (S.trichotomy q)
*-sgn-max {q} {s} {{Sgn[s]}} | AA.1st q≃0 =
  let q*s≃q*sgn[q] =
        begin
          q * s
        ≃⟨ AA.subst₂ q≃0 ⟩
          0 * s
        ≃⟨ AA.absorb ⟩
          0
        ≃˘⟨ AA.absorb ⟩
          0 * ℚ.sgn q
        ≃˘⟨ AA.subst₂ q≃0 ⟩
          q * ℚ.sgn q
        ∎
   in ∨-introᴿ q*s≃q*sgn[q]
*-sgn-max {q} {{ℚ.Sgn[0]}} | AA.2nd pos[q] =
  let neg[-q] = S.neg-Positive pos[q]
      q*0-q*sgn[q]≃[-q] =
        begin
          q * 0 - q * ℚ.sgn q
        ≃⟨ AA.subst₂ AA.absorb ⟩
          0 - q * ℚ.sgn q
        ≃⟨ ℚ.sub-zeroᴸ ⟩
          - (q * ℚ.sgn q)
        ≃⟨ AA.subst₁ (AA.subst₂ (ℚ.sgn[q]≃1-from-pos[q] pos[q])) ⟩
          - (q * 1)
        ≃⟨ AA.subst₁ AA.ident ⟩
          - q
        ∎
      q*0<q*sgn[q] = AA.subst₁ (Eq.sym q*0-q*sgn[q]≃[-q]) neg[-q]
   in ∨-introᴸ q*0<q*sgn[q]
*-sgn-max {q} {{ℚ.Sgn[1]}} | AA.2nd pos[q] =
  let q*1≃q*sgn[q] =
        begin
          q * 1
        ≃˘⟨ AA.subst₂ (ℚ.sgn[q]≃1-from-pos[q] pos[q]) ⟩
          q * ℚ.sgn q
        ∎
   in ∨-introᴿ q*1≃q*sgn[q]
*-sgn-max {q} {{ℚ.Sgn[-1]}} | AA.2nd pos[q] =
  let q*[-1]-q*sgn[q]≃[-[q+q]] =
        begin
          q * -1 - q * ℚ.sgn q
        ≃⟨ AA.subst₂ AA.comm ⟩
          -1 * q - q * ℚ.sgn q
        ≃⟨ AA.subst₂ ℚ.*-neg-ident ⟩
          (- q) - q * ℚ.sgn q
        ≃⟨ AA.subst₂ (AA.subst₂ (ℚ.sgn[q]≃1-from-pos[q] pos[q])) ⟩
          (- q) - q * 1
        ≃⟨ AA.subst₂ AA.ident ⟩
          (- q) - q
        ≃˘⟨ ℚ.neg-sub ⟩
          - (q - (- q))
        ≃⟨ AA.subst₁ ℚ.sub-negᴿ ⟩
          - (q + q)
        ∎
      pos[q+q] = AA.pres pos[q] pos[q]
      neg[-[q+q]] = S.neg-Positive pos[q+q]
      q*[-1]<q*sgn[q] = AA.subst₁ (Eq.sym q*[-1]-q*sgn[q]≃[-[q+q]]) neg[-[q+q]]
   in ∨-introᴸ q*[-1]<q*sgn[q]
*-sgn-max {q} {{ℚ.Sgn[0]}} | AA.3rd neg[q] =
  let q*0-q*sgn[q]≃q =
        begin
          q * 0 - q * ℚ.sgn q
        ≃⟨ AA.subst₂ AA.absorb ⟩
          0 - q * ℚ.sgn q
        ≃⟨ ℚ.sub-zeroᴸ ⟩
          - (q * ℚ.sgn q)
        ≃⟨ AA.subst₁ (AA.subst₂ (ℚ.sgn[q]≃[-1]-from-neg[q] neg[q])) ⟩
          - (q * -1)
        ≃⟨ AA.subst₁ AA.comm ⟩
          - (-1 * q)
        ≃⟨ AA.subst₁ ℚ.*-neg-ident ⟩
          - (- q)
        ≃⟨ AA.inv-involutive ⟩
          q
        ∎
      q*0<q*sgn[q] = AA.subst₁ (Eq.sym q*0-q*sgn[q]≃q) neg[q]
   in ∨-introᴸ q*0<q*sgn[q]
*-sgn-max {q} {{ℚ.Sgn[1]}} | AA.3rd neg[q] =
  let q*1-q*sgn[q]≃q+q =
        begin
          q * 1 - q * ℚ.sgn q
        ≃⟨ AA.subst₂ AA.ident ⟩
          q - q * ℚ.sgn q
        ≃⟨ AA.subst₂ (AA.subst₂ (ℚ.sgn[q]≃[-1]-from-neg[q] neg[q])) ⟩
          q - (q * -1)
        ≃⟨ AA.subst₂ AA.comm ⟩
          q - (-1 * q)
        ≃⟨ AA.subst₂ ℚ.*-neg-ident ⟩
          q - (- q)
        ≃⟨ ℚ.sub-negᴿ ⟩
          q + q
        ∎
      neg[q+q] = AA.pres neg[q] neg[q]
      q*1<q*sgn[q] = AA.subst₁ (Eq.sym q*1-q*sgn[q]≃q+q) neg[q+q]
   in ∨-introᴸ q*1<q*sgn[q]
*-sgn-max {q} {{ℚ.Sgn[-1]}} | AA.3rd neg[q] =
  let q*[-1]≃q*sgn[q] =
        begin
          q * -1
        ≃˘⟨ AA.subst₂ (ℚ.sgn[q]≃[-1]-from-neg[q] neg[q]) ⟩
          q * ℚ.sgn q
        ∎
   in ∨-introᴿ q*[-1]≃q*sgn[q]

abs-triangle : {p q : ℚ} → ℚ.abs (p + q) ≤ ℚ.abs p + ℚ.abs q
abs-triangle {p} {q} =
    R.begin
      ℚ.abs (p + q)
    R.≃⟨ ℚ.abs-defn ⟩
      (p + q) * ℚ.sgn (p + q)
    R.≃⟨ AA.distrib ⟩
      p * ℚ.sgn (p + q) + q * ℚ.sgn (p + q)
    R.≤⟨ AA.subst₂ *-sgn-max ⟩
      p * ℚ.sgn p + q * ℚ.sgn (p + q)
    R.≤⟨ AA.subst₂ *-sgn-max ⟩
      p * ℚ.sgn p + q * ℚ.sgn q
    R.≃˘⟨ AA.subst₂ ℚ.abs-defn ⟩
      ℚ.abs p + q * ℚ.sgn q
    R.≃˘⟨ AA.subst₂ ℚ.abs-defn ⟩
      ℚ.abs p + ℚ.abs q
    R.∎
  where
    module R = Ord.≤-Reasoning
