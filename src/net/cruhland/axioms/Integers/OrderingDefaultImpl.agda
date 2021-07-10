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
open import net.cruhland.axioms.Sign using (Positive; pos≄0)
import net.cruhland.models.Function
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (∧-intro; contra; ¬_)

module net.cruhland.axioms.Integers.OrderingDefaultImpl
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (Z+ : Addition PA ZB)
  (Z- : Negation PA ZB Z+)
  (ZS : Sign PA ZB Z+ Z-)
  (Z* : Multiplication PA ZB Z+ Z- ZS)
  where

private open module ℕ = PeanoArithmetic PA using (ℕ)
private open module ℤB = Base ZB using (ℤ)
private module ℤ* = Multiplication Z*
private module ℤ- = Negation Z-
private module ℤS = Sign ZS

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
  lessThanOrEqual : Ord.LessThanOrEqual ℤ
  lessThanOrEqual = Ord.lessThanOrEqual _≤₀_

  lessThan : Ord.LessThan ℤ
  lessThan = Ord.lessThan _<₀_

  totalOrder : Ord.TotalOrder ℤ
  totalOrder = record { <-from-≤≄ = <₀-intro }

  ≤-antisymmetric : AA.Antisymmetric _≤_
  ≤-antisymmetric = AA.antisymmetric ≤-antisym
    where
      ≤-antisym : {a b : ℤ} → a ≤ b → b ≤ a → a ≃ b
      ≤-antisym {a} {b} (≤₀-intro {d₁} a+d₁≃b) (≤₀-intro {d₂} b+d₂≃a) =
        let d₁+d₂-as-ℤ≃0-as-ℤ =
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
              ≃⟨ ℤB.fromNatLiteral≃casts 0 ⟩
                (0 as ℤ)
              ∎
            ∧-intro _ d₂≃0 = ℕ.+-both-zero (AA.inject d₁+d₂-as-ℤ≃0-as-ℤ)
         in begin
              a
            ≃˘⟨ b+d₂≃a ⟩
              b + (d₂ as ℤ)
            ≃⟨ AA.subst₂ (AA.subst₁ d₂≃0) ⟩
              b + (0 as ℤ)
            ≃˘⟨ AA.subst₂ (ℤB.fromNatLiteral≃casts 0) ⟩
              b + 0
            ≃⟨ AA.ident ⟩
              b
            ∎

<-from-pos : {a b : ℤ} → Positive (b - a) → a < b
<-from-pos {a} {b} pos[b-a] =
  let ℤS.≃posℕ-intro {d} pos[d] b-a≃d = ℤS.posℕ-from-posℤ pos[b-a]
      b≃a+d = ℤ-.≃ᴸ-subᴿ-toᴸ b-a≃d
      a≤b = ≤₀-intro (Eq.sym b≃a+d)
      a≄b = λ a≃b →
        let d-as-ℤ≃0-as-ℤ =
              begin
                (d as ℤ)
              ≃˘⟨ b-a≃d ⟩
                b - a
              ≃⟨ AA.subst₂ a≃b ⟩
                b - b
              ≃⟨ ℤ-.sub-same≃zero ⟩
                0
              ≃⟨ ℤB.fromNatLiteral≃casts 0 ⟩
                (0 as ℤ)
              ∎
         in contra (AA.inject d-as-ℤ≃0-as-ℤ) (pos≄0 pos[d])
   in Ord.<-from-≤≄ a≤b a≄b

pos-from-< : {a b : ℤ} → a < b → Positive (b - a)
pos-from-< {a} {b} (<₀-intro (≤₀-intro {d} a+d≃b) a≄b) =
  let d≄0 = λ d≃0 →
        let a≃b =
              begin
                a
              ≃˘⟨ AA.ident ⟩
                a + 0
              ≃⟨ AA.subst₂ (ℤB.fromNatLiteral≃casts 0) ⟩
                a + (0 as ℕ as ℤ)
              ≃˘⟨ AA.subst₂ (AA.subst₁ d≃0) ⟩
                a + (d as ℤ)
              ≃⟨ a+d≃b ⟩
                b
              ∎
         in contra a≃b a≄b
      pos[d] = ℕ.Pos-intro-≄0 d≄0
      b-a≃d = ℤ-.≃ᴿ-+ᴸ-toᴿ (Eq.sym a+d≃b)
   in ℤS.posℤ-from-posℕ (ℤS.≃posℕ-intro pos[d] b-a≃d)

order-trichotomy : (a b : ℤ) → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
order-trichotomy a b = AA.exactlyOneOfThree 1of3 ¬2of3
  where
    1of3 : AA.OneOfThree (a < b) (a ≃ b) (a > b)
    1of3 with AA.ExactlyOneOfThree.at-least-one (ℤS.trichotomy (b - a))
    ... | AA.1st neg[b-a] = AA.3rd (<-from-pos (ℤ*.sub-sign-swap neg[b-a]))
    ... | AA.2nd b-a≃0 = AA.2nd (Eq.sym (ℤ-.≃-from-zero-sub b-a≃0))
    ... | AA.3rd pos[b-a] = AA.1st (<-from-pos pos[b-a])

    ¬2of3 : ¬ AA.TwoOfThree (a < b) (a ≃ b) (a > b)
    ¬2of3 (AA.1∧2 (<₀-intro a≤b a≄b) a≃b) =
      contra a≃b a≄b
    ¬2of3 (AA.1∧3 (<₀-intro a≤b a≄b) (<₀-intro b≤a b≄a)) =
      contra (AA.antisym a≤b b≤a) a≄b
    ¬2of3 (AA.2∧3 a≃b (<₀-intro b≤a b≄a)) =
      contra a≃b (Eq.sym b≄a)