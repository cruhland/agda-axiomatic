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
open import net.cruhland.axioms.Operators using (_+_; -_; _-_)
open import net.cruhland.axioms.Ordering as Ord using (_≤_; _<_; _>_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (∧-intro; _↯_; ¬_; ¬-intro)

module net.cruhland.axioms.Integers.OrderingDefaultImpl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZA : Addition PA ZB)
  (ZN : Negation PA ZB ZA)
  (ZS : Sign PA ZB ZA ZN)
  (ZM : Multiplication PA ZB ZA ZN ZS)
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

record _<₀_ (a b : ℤ) : Set where
  constructor <₀-intro
  field
    a≤b : a ≤₀ b
    a≄b : a ≄ b

instance
  nonStrictOrder : Ord.NonStrictOrder ℤ
  nonStrictOrder = Ord.nonStrict-from-lte _≤₀_

  strictOrder : Ord.StrictOrder ℤ
  strictOrder = Ord.strict-from-lt _<₀_

  totalOrder : Ord.TotalOrder ℤ
  totalOrder = record { <-from-≤≄ = <₀-intro }

  -- Instances needed in impls only
  lessThanOrEqual = Ord.NonStrictOrder.lte nonStrictOrder
  greaterThanOrEqual = Ord.NonStrictOrder.gte nonStrictOrder
  lessThan = Ord.StrictOrder.lt strictOrder
  greaterThan = Ord.StrictOrder.gt strictOrder

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
   in Ord.<-from-≤≄ a≤b a≄b

pos-from-< : {a b : ℤ} → a < b → S.Positive (b - a)
pos-from-< {a} {b} (<₀-intro (≤₀-intro {d} a+d≃b) a≄b) =
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

order-trichotomy : (a b : ℤ) → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
order-trichotomy a b = AA.exactlyOneOfThree 1of3 ¬2of3
  where
    1of3 : AA.OneOfThree (a < b) (a ≃ b) (a > b)
    1of3 with AA.ExactlyOneOfThree.at-least-one (S.trichotomy (b - a))
    ... | AA.1st b-a≃0 = AA.2nd (Eq.sym (ℤ.≃-from-zero-sub b-a≃0))
    ... | AA.2nd pos[b-a] = AA.1st (<-from-pos pos[b-a])
    ... | AA.3rd neg[b-a] = AA.3rd (<-from-pos (ℤ.sub-sign-swap neg[b-a]))

    ¬2of3 : ¬ AA.TwoOfThree (a < b) (a ≃ b) (a > b)
    ¬2of3 = ¬-intro λ
      { (AA.1∧2 (<₀-intro a≤b a≄b) a≃b) →
          a≃b ↯ a≄b
      ; (AA.1∧3 (<₀-intro a≤b a≄b) (<₀-intro b≤a b≄a)) →
          AA.antisym a≤b b≤a ↯ a≄b
      ; (AA.2∧3 a≃b (<₀-intro b≤a b≄a)) →
          a≃b ↯ Eq.sym b≄a
      }
