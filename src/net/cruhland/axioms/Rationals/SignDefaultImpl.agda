import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_+_; -_; _*_; _/_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Rationals.AdditionDecl using (Addition)
open import net.cruhland.axioms.Rationals.BaseDecl using (Base)
open import net.cruhland.axioms.Rationals.DivisionDecl using (Division)
open import net.cruhland.axioms.Rationals.MultiplicationDecl
  using (Multiplication)
open import net.cruhland.axioms.Rationals.NegationDecl using (Negation)
open import net.cruhland.axioms.Rationals.ReciprocalDecl using (Reciprocal)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; ¬-intro; _↯_)

module net.cruhland.axioms.Rationals.SignDefaultImpl
  (PA : PeanoArithmetic)
  (Z : Integers PA)
  (QB : Base PA Z)
  (QA : Addition PA Z QB)
  (QN : Negation PA Z QB QA)
  (QM : Multiplication PA Z QB QA QN)
  (QR : Reciprocal PA Z QB QA QN QM)
  (QD : Division PA Z QB QA QN QM QR)
  where

import net.cruhland.axioms.Rationals.LiteralImpl PA Z as LiteralImpl
import net.cruhland.axioms.Rationals.SignDecl PA Z as SignDecl

private
  module ℤ = Integers Z
  module ℚ where
    open SignDecl.SignPredefs QB QA QN QM QR QD public
    open Addition QA public
    open Base QB public
    open Division QD public
    open LiteralImpl QB public
    open Multiplication QM public
    open Negation QN public

open ℤ using (ℤ)
open ℚ using (ℚ)

record Positive₀ (q : ℚ) : Set where
  constructor Positive₀-intro
  field
    {a b} : ℤ
    pos[a] : S.Positive a
    pos[b] : S.Positive b
    q≃a/b : let instance b≄0 = S.pos≄0 pos[b] in q ≃ a / b

q≄0-from-pos[q] : {q : ℚ} → Positive₀ q → q ≄ 0
q≄0-from-pos[q] {q} (Positive₀-intro {a} {b} pos[a] pos[b] q≃a/b) =
  Eq.≄-intro λ q≃0 →
    let instance
          b≄0 = S.pos≄0 pos[b]
        a/b≃0 =
          begin
            a / b
          ≃˘⟨ q≃a/b ⟩
            q
          ≃⟨ q≃0 ⟩
            0
          ∎
        a≃0 = ℚ.a≃0-from-a/b≃0 a/b≃0
        a≄0 = S.pos≄0 pos[a]
     in a≃0 ↯ a≄0

instance
  Positive₀-substitutive : AA.Substitutive₁ Positive₀ _≃_ _⟨→⟩_
  Positive₀-substitutive = AA.substitutive₁ pos-subst
    where
      pos-subst : {p q : ℚ} → p ≃ q → Positive₀ p → Positive₀ q
      pos-subst p≃q (Positive₀-intro pos[a] pos[b] p≃a/b) =
        Positive₀-intro pos[a] pos[b] (Eq.trans (Eq.sym p≃q) p≃a/b)

  positivity : S.Positivity ℚ
  positivity = record { Positive = Positive₀ ; pos≄0 = q≄0-from-pos[q] }

record Negative₀ (q : ℚ) : Set where
  constructor Negative₀-intro
  field
    {p} : ℚ
    pos[p] : S.Positive p
    q≃-p : q ≃ - p

q≄0-from-neg[q] : {q : ℚ} → Negative₀ q → q ≄ 0
q≄0-from-neg[q] {q} (Negative₀-intro {p} pos[p] q≃-p) =
  Eq.≄-intro λ q≃0 →
    let p≃0 =
          begin
            p
          ≃˘⟨ AA.inv-involutive ⟩
            - (- p)
          ≃˘⟨ AA.subst₁ q≃-p ⟩
            - q
          ≃⟨ AA.subst₁ q≃0 ⟩
            - 0
          ≃⟨ AA.inv-ident ⟩
            0
          ∎
        p≄0 = S.pos≄0 pos[p]
     in p≃0 ↯ p≄0

instance
  Negative₀-substitutive : AA.Substitutive₁ Negative₀ _≃_ _⟨→⟩_
  Negative₀-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : {q r : ℚ} → q ≃ r → Negative₀ q → Negative₀ r
      neg-subst q≃r (Negative₀-intro pos[p] q≃-p) =
        Negative₀-intro pos[p] (Eq.trans (Eq.sym q≃r) q≃-p)

  negativity : S.Negativity ℚ
  negativity = record { Negative = Negative₀ ; neg≄0 = q≄0-from-neg[q] }

positiveDenominator : (q : ℚ) → ℚ.PositiveDenominator q
positiveDenominator q with ℚ.fraction q
... | ℚ.fraction-intro {q↑} {q↓} {{q↓≄0}} q≃q↑/q↓
    with AA.at-least-one (S.trichotomy q↓)
... | AA.1st q↓≃0 =
  q↓≃0 ↯ q↓≄0
... | AA.2nd pos[q↓] =
  let instance q↓≄0-from-pos = S.pos≄0 pos[q↓]
      q≃q↑/q↓ =
        begin
          q
        ≃⟨ q≃q↑/q↓ ⟩
          (q↑ / q↓) {{q↓≄0}}
        ≃⟨ ℚ.div-ℤ-subst-proof ⟩
          (q↑ / q↓) {{q↓≄0-from-pos}}
        ∎
   in ℚ.positiveDenominator-intro {a = q↑} pos[q↓] q≃q↑/q↓
... | AA.3rd neg[q↓] =
  let pos[-q↓] = S.neg-Negative neg[q↓]
      instance
        -q↓≄0-from-pos = S.pos≄0 pos[-q↓]
        -1≄0 = AA.substᴿ AA.inv-ident (AA.subst₁ ℤ.1≄0)
        -1*q↓≄0 = AA.nonzero-prod {{a≄0 = -1≄0}} {{q↓≄0}}
      q≃[-q↑]/[-q↓] =
        begin
          q
        ≃⟨ q≃q↑/q↓ ⟩
          q↑ / q↓
        ≃˘⟨ AA.cancel ⟩
          ((-1 * q↑) / (-1 * q↓))
        ≃⟨ AA.subst₂ ℤ.neg-mult ⟩
          ((- q↑) / (-1 * q↓)) {{ -1*q↓≄0 }}
        ≃⟨ AA.subst₂ ℤ.neg-mult ⟩
          ((- q↑) / (- q↓)) {{ -q↓≄0-from-pos }}
        ∎
   in ℚ.positiveDenominator-intro {a = - q↑} pos[-q↓] q≃[-q↑]/[-q↓]

instance
  +-preserves-pos : AA.Preserves S.Positive _+_
  +-preserves-pos = AA.preserves +-pres
    where
      +-pres : {p q : ℚ} → S.Positive p → S.Positive q → S.Positive (p + q)
      +-pres
          {p} {q}
          (Positive₀-intro {a} {b} pos[a] pos[b] p≃a/b)
          (Positive₀-intro {c} {d} pos[c] pos[d] q≃c/d) =
        let pos[bd] = AA.pres {A = ℤ} {_⊙_ = _*_} pos[b] pos[d]
            instance
              b≄0 = S.pos≄0 pos[b]
              d≄0 = S.pos≄0 pos[d]
              bd≄0₁ = S.pos≄0 pos[bd]
              bd≄0₂ = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
            p+q≃[ad+bc]/bd =
              begin
                p + q
              ≃⟨ AA.subst₂ p≃a/b ⟩
                (a / b) + q
              ≃⟨ AA.subst₂ q≃c/d ⟩
                (a / b) + (c / d)
              ≃⟨ ℚ.+-div-ℤ ⟩
                ((a * d + b * c) / (b * d)) {{bd≄0₂}}
              ≃⟨ ℚ.div-ℤ-subst-proof ⟩
                ((a * d + b * c) / (b * d)) {{bd≄0₁}}
              ∎
            pos[ad] = AA.pres {A = ℤ} {_⊙_ = _*_} pos[a] pos[d]
            pos[bc] = AA.pres {A = ℤ} {_⊙_ = _*_} pos[b] pos[c]
            pos[ad+bc] = AA.pres {A = ℤ} {_⊙_ = _+_} pos[ad] pos[bc]
         in Positive₀-intro pos[ad+bc] pos[bd] p+q≃[ad+bc]/bd

  sign-trichotomy : S.Trichotomy ℚ
  sign-trichotomy = S.trichotomy-intro tri
    where
      tri : (q : ℚ) → AA.ExactlyOneOfThree (q ≃ 0) (S.Positive q) (S.Negative q)
      tri q = AA.exactlyOneOfThree 1of3 ¬2of3
        where
          1of3 : AA.OneOfThree (q ≃ 0) (S.Positive q) (S.Negative q)
          1of3 with positiveDenominator q
          ... | ℚ.positiveDenominator-intro {a} {b} pos[b] q≃a/b
              with AA.at-least-one (S.trichotomy a)
          ... | AA.1st a≃0 =
            let instance
                  b≄0 = S.pos≄0 pos[b]
                q≃0 =
                  begin
                    q
                  ≃⟨ q≃a/b ⟩
                    a / b
                  ≃⟨ AA.subst₂ a≃0 ⟩
                    0 / b
                  ≃⟨ AA.absorb ⟩
                    0
                  ∎
             in AA.1st q≃0
          ... | AA.2nd pos[a] =
            AA.2nd (Positive₀-intro pos[a] pos[b] q≃a/b)
          ... | AA.3rd neg[a] =
            let instance b≄0 = S.pos≄0 pos[b]
                pos[-a] = S.neg-Negative neg[a]
                pos[-a/b] = Positive₀-intro pos[-a] pos[b] Eq.refl
                q≃-[[-a]/b] =
                  begin
                    q
                  ≃⟨ q≃a/b ⟩
                    a / b
                  ≃˘⟨ AA.inv-involutive ⟩
                    - (- (a / b))
                  ≃⟨ AA.subst₁ AA.fnOpCommᴸ ⟩
                    - ((- a) / b)
                  ∎
             in AA.3rd (Negative₀-intro pos[-a/b] q≃-[[-a]/b])

          ¬2of3 : ¬ AA.TwoOfThree (q ≃ 0) (S.Positive q) (S.Negative q)
          ¬2of3 = ¬-intro λ
            { (AA.1∧2 q≃0 pos[q]) →
                q≃0 ↯ S.pos≄0 pos[q]
            ; (AA.1∧3 q≃0 neg[q]) →
                q≃0 ↯ S.neg≄0 neg[q]
            ; (AA.2∧3 pos[q] (Negative₀-intro {p} pos[p] q≃-p)) →
                let p+q≃0 =
                      begin
                        p + q
                      ≃⟨ AA.subst₂ q≃-p ⟩
                        p + (- p)
                      ≃⟨ AA.inv ⟩
                        0
                      ∎
                    pos[p+q] = AA.pres pos[p] pos[q]
                    p+q≄0 = S.pos≄0 pos[p+q]
                 in p+q≃0 ↯ p+q≄0
            }

neg-Positive : {q : ℚ} → S.Positive q → S.Negative (- q)
neg-Positive pos[q] = Negative₀-intro pos[q] Eq.refl

neg-Negative : {q : ℚ} → S.Negative q → S.Positive (- q)
neg-Negative {q} (Negative₀-intro {p} pos[p] q≃-p) =
  let p≃-q =
        begin
          p
        ≃˘⟨ AA.inv-involutive ⟩
          - (- p)
        ≃˘⟨ AA.subst₁ q≃-p ⟩
          - q
        ∎
   in AA.subst₁ p≃-q pos[p]

instance
  positivity-common : S.PositivityCommon ℚ
  positivity-common = record {}

  sign-common : S.SignCommon ℚ
  sign-common =
    record { neg-Positive = neg-Positive ; neg-Negative = neg-Negative }
