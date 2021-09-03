import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_; _value_)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers using (Integers)
open import net.cruhland.axioms.Operators using (_+_; -_; _-_; _*_; _/_)
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
open import net.cruhland.models.Logic
  using (_∧_; ∧-intro; ∨-introᴸ; ∨-introᴿ; _↯_; ¬_; ¬-intro; no; yes)

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
  module ℕ = PeanoArithmetic PA
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
        [-q↓]≄0-from-pos = S.pos≄0 pos[-q↓]
        [-1]*q↓≄0 = AA.nonzero-prod {{a≄0 = ℤ.[-1]≄0}} {{q↓≄0}}
      q≃[-q↑]/[-q↓] =
        begin
          q
        ≃⟨ q≃q↑/q↓ ⟩
          q↑ / q↓
        ≃˘⟨ AA.cancel ⟩
          ((-1 * q↑) / (-1 * q↓))
        ≃⟨ AA.subst₂ ℤ.neg-mult ⟩
          ((- q↑) / (-1 * q↓)) {{[-1]*q↓≄0}}
        ≃⟨ AA.subst₂ ℤ.neg-mult ⟩
          ((- q↑) / (- q↓)) {{[-q↓]≄0-from-pos}}
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

  +-preserves-neg : AA.Preserves S.Negative _+_
  +-preserves-neg = AA.preserves +-pres-neg
    where
      +-pres-neg : {p q : ℚ} → S.Negative p → S.Negative q → S.Negative (p + q)
      +-pres-neg
          {p} {q}
          (Negative₀-intro {b} pos[b] p≃-b) (Negative₀-intro {d} pos[d] q≃-d) =
        let pos[b+d] = AA.pres pos[b] pos[d]
            p+q≃-[b+d] =
              begin
                p + q
              ≃⟨ AA.subst₂ p≃-b ⟩
                (- b) + q
              ≃⟨ AA.subst₂ q≃-d ⟩
                (- b) + (- d)
              ≃˘⟨ AA.compat₂ ⟩
                - (b + d)
              ∎
         in Negative₀-intro pos[b+d] p+q≃-[b+d]

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

  *-preserves-pos : AA.Preserves S.Positive _*_
  *-preserves-pos = AA.preserves *-pres-pos
    where
      *-pres-pos : {p q : ℚ} → S.Positive p → S.Positive q → S.Positive (p * q)
      *-pres-pos
          {p} {q}
          (Positive₀-intro {a} {b} pos[a] pos[b] p≃a/b)
          (Positive₀-intro {c} {d} pos[c] pos[d] q≃c/d) =
        let pos[ac] = AA.pres pos[a] pos[c]
            pos[bd] = AA.pres pos[b] pos[d]
            instance
              b≄0 = S.pos≄0 pos[b]
              d≄0 = S.pos≄0 pos[d]
              bd≄0₁ = AA.nonzero-prod {{a≄0 = b≄0}} {{d≄0}}
              bd≄0₂ = S.pos≄0 pos[bd]
            pq≃ac/bd =
              begin
                p * q
              ≃⟨ AA.subst₂ p≃a/b ⟩
                (a / b) * q
              ≃⟨ AA.subst₂ q≃c/d ⟩
                (a / b) * (c / d)
              ≃⟨ ℚ.*-div-ℤ ⟩
                ((a * c) / (b * d)) {{bd≄0₁}}
              ≃⟨ ℚ.div-ℤ-subst-proof ⟩
                ((a * c) / (b * d)) {{bd≄0₂}}
              ∎
         in Positive₀-intro pos[ac] pos[bd] pq≃ac/bd

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

neg*pos≃neg : {p q : ℚ} → S.Negative p → S.Positive q → S.Negative (p * q)
neg*pos≃neg {p} {q} (Negative₀-intro {r} pos[r] p≃-r) pos[q] =
  let pos[rq] = AA.pres pos[r] pos[q]
      pq≃-[rq] =
        begin
          p * q
        ≃⟨ AA.subst₂ p≃-r ⟩
          (- r) * q
        ≃˘⟨ AA.fnOpCommᴸ ⟩
          - (r * q)
        ∎
   in Negative₀-intro pos[rq] pq≃-[rq]

neg*neg≃pos : {p q : ℚ} → S.Negative p → S.Negative q → S.Positive (p * q)
neg*neg≃pos
    {p} {q}
    (Negative₀-intro {r} pos[r] p≃-r) (Negative₀-intro {s} pos[s] q≃-s) =
  let pos[rs] = AA.pres pos[r] pos[s]
      pq≃rs =
        begin
          p * q
        ≃⟨ AA.subst₂ p≃-r ⟩
          (- r) * q
        ≃⟨ AA.subst₂ q≃-s ⟩
          (- r) * (- s)
        ≃˘⟨ AA.fnOpCommᴸ ⟩
          - (r * (- s))
        ≃˘⟨ AA.subst₁ AA.fnOpCommᴿ ⟩
          - (- (r * s))
        ≃⟨ AA.inv-involutive ⟩
          r * s
        ∎
      pos[pq] = AA.subst₁ (Eq.sym pq≃rs) pos[rs]
   in pos[pq]

instance
  positivity-common : S.PositivityCommon ℚ
  positivity-common = record {}

  negativity-common : S.NegativityCommon ℚ
  negativity-common = record {}

  sign-common : S.SignCommon ℚ
  sign-common =
    record { neg-Positive = neg-Positive ; neg-Negative = neg-Negative }

sgn : ℚ → ℚ
sgn q with AA.at-least-one (S.trichotomy q)
... | AA.1st q≃0 = 0
... | AA.2nd pos[q] = 1
... | AA.3rd neg[q] = -1

sgn[q]≃0-from-q≃0 : {q : ℚ} → q ≃ 0 → sgn q ≃ 0
sgn[q]≃0-from-q≃0 {q} q≃0 with AA.at-least-one (S.trichotomy q)
... | AA.1st q≃0 = Eq.refl
... | AA.2nd pos[q] = q≃0 ↯ S.pos≄0 pos[q]
... | AA.3rd neg[q] = q≃0 ↯ S.neg≄0 neg[q]

sgn[q]≃1-from-pos[q] : {q : ℚ} → S.Positive q → sgn q ≃ 1
sgn[q]≃1-from-pos[q] {q} pos[q] with AA.at-least-one (S.trichotomy q)
... | AA.1st q≃0 =
  q≃0 ↯ S.pos≄0 pos[q]
... | AA.2nd pos[q] =
  Eq.refl
... | AA.3rd neg[q] =
  let 2of3 = AA.2∧3 pos[q] neg[q]
      ¬2of3 = AA.at-most-one (S.trichotomy q)
   in 2of3 ↯ ¬2of3

sgn[q]≃[-1]-from-neg[q] : {q : ℚ} → S.Negative q → sgn q ≃ -1
sgn[q]≃[-1]-from-neg[q] {q} neg[q] with AA.at-least-one (S.trichotomy q)
... | AA.1st q≃0 =
  q≃0 ↯ S.neg≄0 neg[q]
... | AA.2nd pos[q] =
  let 2of3 = AA.2∧3 pos[q] neg[q]
      ¬2of3 = AA.at-most-one (S.trichotomy q)
   in 2of3 ↯ ¬2of3
... | AA.3rd neg[q] =
  Eq.refl

q≃0-from-sgn[q]≃0 : {q : ℚ} → sgn q ≃ 0 → q ≃ 0
q≃0-from-sgn[q]≃0 {q} sgn[q]≃0 with AA.at-least-one (S.trichotomy q)
... | AA.1st q≃0 =
  q≃0
... | AA.2nd pos[q] =
  let 1≃0 = sgn[q]≃0
   in 1≃0 ↯ ℚ.1≄0
... | AA.3rd neg[q] =
  let [-1]≃0 = sgn[q]≃0
   in [-1]≃0 ↯ ℚ.[-1]≄0

[-1]≄1 : -1 ≄ (ℚ value 1)
[-1]≄1 = Eq.≄-intro λ [-1]≃1 →
  let 0:ℤ:ℚ≃2:ℤ:ℚ =
        begin
          0
        ≃˘⟨ AA.inv ⟩
          -1 + 1
        ≃⟨ AA.subst₂ [-1]≃1 ⟩
          1 + 1
        ≃⟨⟩
          (ℕ.step 0 as ℤ as ℚ) + (ℕ.step 0 as ℤ as ℚ)
        ≃˘⟨ AA.compat₂ ⟩
          ((ℕ.step 0 as ℤ) + (ℕ.step 0 as ℤ) as ℚ)
        ≃˘⟨ AA.subst₁ AA.compat₂ ⟩
          (ℕ.step 0 + ℕ.step 0 as ℤ as ℚ)
        ≃˘⟨ AA.subst₁ (AA.subst₁ AA.fnOpCommᴿ) ⟩
          (ℕ.step (ℕ.step 0 + 0) as ℤ as ℚ)
        ≃⟨ AA.subst₁ (AA.subst₁ AA.fnOpCommᴸ) ⟩
          (ℕ.step (ℕ.step 0) + 0 as ℤ as ℚ)
        ≃⟨ AA.subst₁ (AA.subst₁ AA.ident) ⟩
          (ℕ.step (ℕ.step 0) as ℤ as ℚ)
        ≃⟨⟩
          2
        ∎
      0:ℤ:ℚ≄2:ℤ:ℚ = Eq.sym (AA.subst₁ (AA.subst₁ ℕ.step≄zero))
   in 0:ℤ:ℚ≃2:ℤ:ℚ ↯ 0:ℤ:ℚ≄2:ℤ:ℚ

q≃0-from-q≃[-q] : {q : ℚ} → q ≃ - q → q ≃ 0
q≃0-from-q≃[-q] {q} q≃[-q] with q ≃? 0
... | yes q≃0 =
  q≃0
... | no q≄0 =
  let instance
        _ = q≄0
      [-1]≃1 =
        begin
          -1
        ≃⟨⟩
          - 1
        ≃˘⟨ AA.subst₁ ℚ.q/q≃1 ⟩
          - (q / q)
        ≃⟨ AA.fnOpCommᴸ ⟩
          (- q) / q
        ≃˘⟨ AA.subst₂ q≃[-q] ⟩
          q / q
        ≃⟨ ℚ.q/q≃1 ⟩
          1
        ∎
   in [-1]≃1 ↯ [-1]≄1

pos[q]-from-sgn[q]≃1 : {q : ℚ} → sgn q ≃ 1 → S.Positive q
pos[q]-from-sgn[q]≃1 {q} sgn[q]≃1 with AA.at-least-one (S.trichotomy q)
... | AA.1st q≃0 =
  let 1≃0 = Eq.sym sgn[q]≃1
   in 1≃0 ↯ ℚ.1≄0
... | AA.2nd pos[q] =
  pos[q]
... | AA.3rd neg[q] =
  let [-1]≃1 = sgn[q]≃1
   in [-1]≃1 ↯ [-1]≄1

neg[q]-from-sgn[q]≃[-1] : {q : ℚ} → sgn q ≃ -1 → S.Negative q
neg[q]-from-sgn[q]≃[-1] {q} sgn[q]≃[-1] with AA.at-least-one (S.trichotomy q)
... | AA.1st q≃0 =
  let [-1]≃0 = Eq.sym sgn[q]≃[-1]
      1≃0 =
        begin
          1
        ≃˘⟨ AA.inv-involutive ⟩
          - (- 1)
        ≃⟨ AA.subst₁ [-1]≃0 ⟩
          - 0
        ≃⟨ AA.inv-ident ⟩
          0
        ∎
   in 1≃0 ↯ ℚ.1≄0
... | AA.2nd pos[q] =
  let [-1]≃1 = Eq.sym sgn[q]≃[-1]
   in [-1]≃1 ↯ [-1]≄1
... | AA.3rd neg[q] =
  neg[q]

instance
  sgn-substitutive : AA.Substitutive₁ sgn _≃_ _≃_
  sgn-substitutive = AA.substitutive₁ sgn-subst
    where
      sgn-subst : {p q : ℚ} → p ≃ q → sgn p ≃ sgn q
      sgn-subst {p} {q} p≃q with AA.at-least-one (S.trichotomy q)
      ... | AA.1st q≃0 =
        sgn[q]≃0-from-q≃0 (Eq.trans p≃q q≃0)
      ... | AA.2nd pos[q] =
        sgn[q]≃1-from-pos[q] (AA.subst₁ (Eq.sym p≃q) pos[q])
      ... | AA.3rd neg[q] =
        sgn[q]≃[-1]-from-neg[q] (AA.subst₁ (Eq.sym p≃q) neg[q])

abs : ℚ → ℚ
abs q = q * sgn q

abs[q]≃0-from-q≃0 : {q : ℚ} → q ≃ 0 → abs q ≃ 0
abs[q]≃0-from-q≃0 {q} q≃0 =
  begin
    abs q
  ≃⟨⟩
    q * sgn q
  ≃⟨ AA.subst₂ (sgn[q]≃0-from-q≃0 q≃0) ⟩
    q * 0
  ≃⟨ AA.absorb ⟩
    0
  ∎

abs[q]≃q-from-pos[q] : {q : ℚ} → S.Positive q → abs q ≃ q
abs[q]≃q-from-pos[q] {q} pos[q] =
  begin
    abs q
  ≃⟨⟩
    q * sgn q
  ≃⟨ AA.subst₂ (sgn[q]≃1-from-pos[q] pos[q]) ⟩
    q * 1
  ≃⟨ AA.ident ⟩
    q
  ∎

abs[q]≃[-q]-from-neg[q] : {q : ℚ} → S.Negative q → abs q ≃ - q
abs[q]≃[-q]-from-neg[q] {q} neg[q] =
  begin
    abs q
  ≃⟨⟩
    q * sgn q
  ≃⟨ AA.subst₂ (sgn[q]≃[-1]-from-neg[q] neg[q]) ⟩
    q * -1
  ≃⟨ AA.comm ⟩
    -1 * q
  ≃⟨ ℚ.*-neg-ident ⟩
    - q
  ∎

q≃0-from-abs[q]≃0 : {q : ℚ} → abs q ≃ 0 → q ≃ 0
q≃0-from-abs[q]≃0 q*sgn[q]≃0 with AA.zero-prod q*sgn[q]≃0
... | ∨-introᴸ q≃0 = q≃0
... | ∨-introᴿ sgn[q]≃0 = q≃0-from-sgn[q]≃0 sgn[q]≃0

¬neg[q]-from-abs[q]≃q : {q : ℚ} → abs q ≃ q → ¬ S.Negative q
¬neg[q]-from-abs[q]≃q abs[q]≃q = ¬-intro λ neg[q] →
  let abs[q]≃[-q] = abs[q]≃[-q]-from-neg[q] neg[q]
      q≃[-q] = Eq.trans (Eq.sym abs[q]≃q) abs[q]≃[-q]
      q≃0 = q≃0-from-q≃[-q] q≃[-q]
   in q≃0 ↯ S.neg≄0 neg[q]

¬pos[q]-from-abs[q]≃[-q] : {q : ℚ} → abs q ≃ - q → ¬ S.Positive q
¬pos[q]-from-abs[q]≃[-q] abs[q]≃[-q] = ¬-intro λ pos[q] →
  let abs[q]≃q = abs[q]≃q-from-pos[q] pos[q]
      q≃[-q] = Eq.trans (Eq.sym abs[q]≃q) abs[q]≃[-q]
      q≃0 = q≃0-from-q≃[-q] q≃[-q]
   in q≃0 ↯ S.pos≄0 pos[q]

instance
  abs-substitutive : AA.Substitutive₁ abs _≃_ _≃_
  abs-substitutive = AA.substitutive₁ abs-subst
    where
      abs-subst : {p q : ℚ} → p ≃ q → abs p ≃ abs q
      abs-subst {p} {q} p≃q =
        begin
          abs p
        ≃⟨⟩
          p * sgn p
        ≃⟨ AA.subst₂ p≃q ⟩
          q * sgn p
        ≃⟨ AA.subst₂ (AA.subst₁ p≃q) ⟩
          q * sgn q
        ≃⟨⟩
          abs q
        ∎

dist : ℚ → ℚ → ℚ
dist p q = abs (p - q)
