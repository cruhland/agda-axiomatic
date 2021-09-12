import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.MultiplicationDecl
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Integers.SignDecl using (Sign)
open import net.cruhland.axioms.Operators as Op
  using (_+_; -_; _-_; _≤_; _≥_; _<_; _>_)
import net.cruhland.axioms.Ordering as Ord
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_; flip)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (∧-intro; _↯_; ¬_; ¬-intro)

module net.cruhland.axioms.Integers.OrderingDefaultImpl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZA : Addition PA ZB)
  (ZN : Negation PA ZB ZA)
  (ZM : Multiplication PA ZB ZA ZN)
  (ZS : Sign PA ZB ZA ZN ZM)
  where

import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl

private
  module ℕ = PeanoArithmetic PA
  module ℤ where
    open Base ZB public
    open LiteralImpl ZB public
    open Multiplication ZM public
    open Negation ZN public
    open Sign ZS public

open ℕ using (ℕ)
open ℤ using (ℤ)

record _≤₀_ (a b : ℤ) : Set where
  constructor ≤₀-intro
  field
    {d} : ℕ
    a+d≃b : a + (d as ℤ) ≃ b

≤₀-from-≃ : {a b : ℤ} → a ≃ b → a ≤₀ b
≤₀-from-≃ {a} {b} a≃b =
  let a+0≃b =
        begin
          a + 0
        ≃⟨ AA.ident ⟩
          a
        ≃⟨ a≃b ⟩
          b
        ∎
   in ≤₀-intro a+0≃b

record _<₀_ (a b : ℤ) : Set where
  constructor <₀-intro
  field
    a≤b : a ≤₀ b
    a≄b : a ≄ b

instance
  ltEq : Op.LtEq ℤ
  ltEq = Op.ltEq _≤₀_

  gtEq : Op.GtEq ℤ
  gtEq = Op.gtEq (flip _≤_)

  ≤-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _≤_ _≃_ _⟨→⟩_
  ≤-substitutiveᴸ = AA.substitutive₂ ≤-substᴸ
    where
      ≤-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ ≤ b → a₂ ≤ b
      ≤-substᴸ {a₁} {a₂} {b} a₁≃a₂ (≤₀-intro {d} a₁+d≃b) =
        let a₂+d≃b =
              begin
                a₂ + (d as ℤ)
              ≃˘⟨ AA.subst₂ a₁≃a₂ ⟩
                a₁ + (d as ℤ)
              ≃⟨ a₁+d≃b ⟩
                b
              ∎
         in ≤₀-intro a₂+d≃b

  ≤-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _≤_ _≃_ _⟨→⟩_
  ≤-substitutiveᴿ = AA.substitutive₂ ≤-substᴿ
    where
      ≤-substᴿ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → b ≤ a₁ → b ≤ a₂
      ≤-substᴿ a₁≃a₂ (≤₀-intro b+d≃a₁) = ≤₀-intro (Eq.trans b+d≃a₁ a₁≃a₂)

  ≤-substitutive : AA.Substitutive² _≤_ _≃_ _⟨→⟩_
  ≤-substitutive = AA.substitutive² {A = ℤ}

  ≤-reflexive : Eq.Reflexive _≤_
  ≤-reflexive = Eq.reflexive (≤₀-intro AA.ident)

  ≤-transitive : Eq.Transitive _≤_
  ≤-transitive = Eq.transitive ≤-trans
    where
      ≤-trans : {a b c : ℤ} → a ≤ b → b ≤ c → a ≤ c
      ≤-trans {a} {b} {c} (≤₀-intro {d₁} a+d₁≃b) (≤₀-intro {d₂} b+d₂≃c) =
        let a+[d₁+d₂]≃c =
              begin
                a + (d₁ + d₂ as ℤ)
              ≃⟨ AA.subst₂ AA.compat₂ ⟩
                a + ((d₁ as ℤ) + (d₂ as ℤ))
              ≃˘⟨ AA.assoc ⟩
                (a + (d₁ as ℤ)) + (d₂ as ℤ)
              ≃⟨ AA.subst₂ a+d₁≃b ⟩
                b + (d₂ as ℤ)
              ≃⟨ b+d₂≃c ⟩
                c
              ∎
         in ≤₀-intro a+[d₁+d₂]≃c

  ≤-antisymmetric : AA.Antisymmetric _≤_
  ≤-antisymmetric = AA.antisymmetric ≤-antisym
    where
      ≤-antisym : {a b : ℤ} → a ≤ b → b ≤ a → a ≃ b
      ≤-antisym {a} {b} (≤₀-intro {d₁} a+d₁≃b) (≤₀-intro {d₂} b+d₂≃a) =
        let d₁+d₂:ℤ≃0:ℤ =
              begin
                (d₁ + d₂ as ℤ)
              ≃⟨ AA.compat₂ ⟩
                (d₁ as ℤ) + (d₂ as ℤ)
              ≃˘⟨ AA.ident ⟩
                0 + ((d₁ as ℤ) + (d₂ as ℤ))
              ≃˘⟨ AA.subst₂ AA.inv ⟩
                ((- a) + a) + ((d₁ as ℤ) + (d₂ as ℤ))
              ≃⟨ AA.assoc ⟩
                (- a) + (a + ((d₁ as ℤ) + (d₂ as ℤ)))
              ≃˘⟨ AA.subst₂ AA.assoc ⟩
                (- a) + ((a + (d₁ as ℤ)) + (d₂ as ℤ))
              ≃⟨ AA.subst₂ (AA.subst₂ a+d₁≃b) ⟩
                (- a) + (b + (d₂ as ℤ))
              ≃⟨ AA.subst₂ b+d₂≃a ⟩
                (- a) + a
              ≃⟨ AA.inv ⟩
                0
              ≃⟨⟩
                (0 as ℤ)
              ∎
            ∧-intro _ d₂≃0 = ℕ.+-both-zero (AA.inject d₁+d₂:ℤ≃0:ℤ)
         in begin
              a
            ≃˘⟨ b+d₂≃a ⟩
              b + (d₂ as ℤ)
            ≃⟨ AA.subst₂ (AA.subst₁ d₂≃0) ⟩
              b + (0 as ℤ)
            ≃⟨⟩
              b + 0
            ≃⟨ AA.ident ⟩
              b
            ∎

  lessThanOrEqual : Ord.NonStrict _≤_
  lessThanOrEqual = Ord.nonstrict-intro ≤₀-from-≃

  nonStrictOrder : Ord.NonStrict² _≤_ (flip _≤_)
  nonStrictOrder = Ord.nonstrict²-from-nonstrict {A = ℤ}

  lt : Op.Lt ℤ
  lt = Ord.lt-≤≄

  gt : Op.Gt ℤ
  gt = Ord.gt-flip-≤≄

  lessThan : Ord.Strict {A = ℤ} Ord._≤≄_
  lessThan = Ord.strict-from-nonstrict

  strictOrder : Ord.Strict² Ord._≤≄_ (flip Ord._≤≄_)
  strictOrder = Ord.strict²-from-strict

  -- Instances needed in impls only
  greaterThanOrEqual = Ord.NonStrict².gte nonStrictOrder
  greaterThan = Ord.Strict².gt strictOrder

<-from-pos : {a b : ℤ} → S.Positive (b - a) → a < b
<-from-pos {a} {b} pos[b-a] =
  let ℤ.≃posℕ-intro {d} pos[d] b-a≃d = ℤ.posℕ-from-posℤ pos[b-a]
      b≃a+d = ℤ.≃ᴸ-subᴿ-toᴸ b-a≃d
      a≤b = ≤₀-intro (Eq.sym b≃a+d)
      a≄b = Eq.≄-intro λ a≃b →
        let d:ℤ≃0:ℤ =
              begin
                (d as ℤ)
              ≃˘⟨ b-a≃d ⟩
                b - a
              ≃⟨ AA.subst₂ a≃b ⟩
                b - b
              ≃⟨ ℤ.sub-same≃zero ⟩
                0
              ≃⟨⟩
                (0 as ℤ)
              ∎
            d≃0 = AA.inject d:ℤ≃0:ℤ
            d≄0 = S.pos≄0 pos[d]
         in d≃0 ↯ d≄0
   in Ord.≤≄-intro a≤b a≄b

pos-from-< : {a b : ℤ} → a < b → S.Positive (b - a)
pos-from-< {a} {b} (Ord.≤≄-intro (≤₀-intro {d} a+d≃b) a≄b) =
  let d≄0 = Eq.≄-intro λ d≃0 →
        let a≃b =
              begin
                a
              ≃˘⟨ AA.ident ⟩
                a + 0
              ≃⟨⟩
                a + (0 as ℤ)
              ≃˘⟨ AA.subst₂ (AA.subst₁ d≃0) ⟩
                a + (d as ℤ)
              ≃⟨ a+d≃b ⟩
                b
              ∎
         in a≃b ↯ a≄b
      pos[d] = ℕ.Pos-intro-≄0 d≄0
      b-a≃d = ℤ.≃ᴿ-+ᴸ-toᴿ (Eq.sym a+d≃b)
   in ℤ.posℤ-from-posℕ (ℤ.≃posℕ-intro pos[d] b-a≃d)

instance
  order-trichotomy : Ord.Trichotomy _<_ _>_
  order-trichotomy = Ord.trichotomy-intro ord-tri
    where
      ord-tri : (a b : ℤ) → AA.ExactlyOneOfThree (a ≃ b) (a < b) (a > b)
      ord-tri a b = AA.exactlyOneOfThree 1of3 ¬2of3
        where
          1of3 : AA.OneOfThree (a ≃ b) (a < b) (a > b)
          1of3 with AA.at-least-one (S.trichotomy (b - a))
          ... | AA.1st b-a≃0 = AA.1st (Eq.sym (ℤ.≃-from-zero-sub b-a≃0))
          ... | AA.2nd pos[b-a] = AA.2nd (<-from-pos pos[b-a])
          ... | AA.3rd neg[b-a] = AA.3rd (<-from-pos (ℤ.sub-sign-swap neg[b-a]))

          ¬2of3 : ¬ AA.TwoOfThree (a ≃ b) (a < b) (a > b)
          ¬2of3 = ¬-intro λ
            { (AA.1∧2 a≃b (Ord.≤≄-intro a≤b a≄b)) →
                a≃b ↯ a≄b
            ; (AA.1∧3 a≃b (Ord.≤≄-intro b≤a b≄a)) →
                a≃b ↯ Eq.sym b≄a
            ; (AA.2∧3 (Ord.≤≄-intro a≤b a≄b) (Ord.≤≄-intro b≤a b≄a)) →
                AA.antisym a≤b b≤a ↯ a≄b
            }

  totalOrder : Ord.TotalOrder _≤_ _≥_ _<_ _>_
  totalOrder = record { lt-from-lte-≄ = Ord.≤≄-intro }
