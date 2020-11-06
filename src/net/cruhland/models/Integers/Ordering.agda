-- Needed for positive integer literals
import Agda.Builtin.FromNat as FromNat
open import Function using (flip)
open import Relation.Nullary.Decidable using (False)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq; ≄-derive)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; ¬sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using
  (⊤; ∧-elimᴿ; ∨-introᴸ; ∨-introᴿ; ⊥-elim; ¬_; Dec; no; yes)

module net.cruhland.models.Integers.Ordering (PA : PeanoArithmetic) where

open module ℕ = PeanoArithmetic PA using (ℕ)
import net.cruhland.models.Integers.Addition PA as Addition
open Addition using (+-identityᴸ; +-identityᴿ)
open import net.cruhland.models.Integers.Base PA using (ℤ)
import net.cruhland.models.Integers.Equality PA as Equality
import net.cruhland.models.Integers.Multiplication PA as Multiplication
open Multiplication using (*-distrib-subᴸ; sub-sign-swap)
import net.cruhland.models.Integers.Negation PA as Negation
open Negation using
  ( +-inverseᴸ; +-inverseᴿ; IsPositive; neg; nil; pos
  ; sub-substᴸ; sub-substᴿ; ≃ᴸ-subᴿ-toᴸ; Trichotomy; trichotomy
  )

infix 4 _≤_
record _≤_ (n m : ℤ) : Set where
  constructor ≤-intro
  field
    a : ℕ
    n≃m+a : m ≃ n + (a as ℤ)

infix 4 _<_
record _<_ (n m : ℤ) : Set where
  constructor <-intro
  field
    n≤m : n ≤ m
    n≄m : n ≄ m

infix 4 _>_
_>_ = flip _<_

≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≃ b
≤-antisym {a} {b} (≤-intro n₁ b≃a+n₁) (≤-intro n₂ a≃b+n₂) =
  let n₁+n₂≃0 =
        begin
          (n₁ + n₂ as ℤ)
        ≃⟨ AA.compat ⟩
          (n₁ as ℤ) + (n₂ as ℤ)
        ≃˘⟨ +-identityᴸ ⟩
          0 + ((n₁ as ℤ) + (n₂ as ℤ))
        ≃˘⟨ AA.substᴸ +-inverseᴸ ⟩
          (- a) + a + ((n₁ as ℤ) + (n₂ as ℤ))
        ≃⟨ AA.assoc ⟩
          (- a) + (a + ((n₁ as ℤ) + (n₂ as ℤ)))
        ≃˘⟨ AA.substᴿ AA.assoc ⟩
          (- a) + (a + (n₁ as ℤ) + (n₂ as ℤ))
        ≃˘⟨ AA.substᴿ (AA.substᴸ b≃a+n₁) ⟩
          (- a) + (b + (n₂ as ℤ))
        ≃˘⟨ AA.substᴿ a≃b+n₂ ⟩
          (- a) + a
        ≃⟨ +-inverseᴸ ⟩
          0
        ∎
      n₂≃0 = ∧-elimᴿ (ℕ.+-both-zero (AA.inject n₁+n₂≃0))
   in trans (trans a≃b+n₂ (AA.substᴿ (AA.subst n₂≃0))) +-identityᴿ

pos→< : ∀ {x y} → IsPositive (y - x) → x < y
pos→< {x} {y} record { n = n ; pos = n≄0 ; x≃n = y-x≃n } =
    <-intro (≤-intro n (≃ᴸ-subᴿ-toᴸ y-x≃n)) x≄y
  where
    x≄y : x ≄ y
    x≄y x≃y = n≄0 (AA.inject n≃0)
      where
        n≃0 =
          begin
            (n as ℤ)
          ≃˘⟨ y-x≃n ⟩
            y - x
          ≃⟨ sub-substᴿ x≃y ⟩
            y - y
          ≃⟨ +-inverseᴿ {y} ⟩
            0
          ∎

data OneOfThree (A B C : Set) : Set where
  1st : A → OneOfThree A B C
  2nd : B → OneOfThree A B C
  3rd : C → OneOfThree A B C

data TwoOfThree (A B C : Set) : Set where
  1∧2 : A → B → TwoOfThree A B C
  1∧3 : A → C → TwoOfThree A B C
  2∧3 : B → C → TwoOfThree A B C

record ExactlyOneOf (A B C : Set) : Set where
  field
    at-least-one : OneOfThree A B C
    at-most-one : ¬ TwoOfThree A B C

open ExactlyOneOf using (at-least-one)

order-trichotomy : ∀ a b → ExactlyOneOf (a < b) (a ≃ b) (a > b)
order-trichotomy a b = record { at-least-one = 1≤ ; at-most-one = ≤1 }
  where
    1≤ : OneOfThree (a < b) (a ≃ b) (a > b)
    1≤ with Trichotomy.at-least (trichotomy (b - a))
    1≤ | nil b-a≃0 = 2nd (sym (trans (≃ᴸ-subᴿ-toᴸ b-a≃0) +-identityᴿ))
    1≤ | pos b-a>0 = 1st (pos→< b-a>0)
    1≤ | neg b-a<0 = 3rd (pos→< (sub-sign-swap {b} b-a<0))

    ≤1 : ¬ TwoOfThree (a < b) (a ≃ b) (a > b)
    ≤1 (1∧2 (<-intro a≤b a≄b) a≃b) = a≄b a≃b
    ≤1 (1∧3 (<-intro a≤b a≄b) (<-intro b≤a b≄a)) = a≄b (≤-antisym a≤b b≤a)
    ≤1 (2∧3 a≃b (<-intro b≤a b≄a)) = b≄a (sym a≃b)

instance
  decEq : DecEq ℤ
  decEq = record { Constraint = λ _ _ → ⊤ ; _≃?_ = _≃?₀_ }
    where
      _≃?₀_ : (a b : ℤ) {{_ : ⊤}} → Dec (a ≃ b)
      a ≃?₀ b with at-least-one (order-trichotomy a b)
      a ≃?₀ b | 1st (<-intro a≤b a≄b) = no a≄b
      a ≃?₀ b | 2nd a≃b = yes a≃b
      a ≃?₀ b | 3rd (<-intro b≤a b≄a) = no (¬sym b≄a)

  *-cancellativeᴸ : AA.Cancellativeᴸ _*_
  *-cancellativeᴸ = record { Constraint = Constraint ; cancelᴸ = *-cancelᴸ }
    where
      Constraint = λ a → False (a ≃? 0)

      *-cancelᴸ : {a b c : ℤ} {{_ : Constraint a}} → a * b ≃ a * c → b ≃ c
      *-cancelᴸ {a} {b} {c} ab≃ac with
        let a[b-c]≃0 =
              begin
                a * (b - c)
              ≃⟨ *-distrib-subᴸ ⟩
                a * b - a * c
              ≃⟨ sub-substᴸ ab≃ac ⟩
                a * c - a * c
              ≃⟨ +-inverseᴿ ⟩
                0
              ∎
         in AA.zero-prod a[b-c]≃0
      *-cancelᴸ {a} {b} {c} ab≃ac | ∨-introᴸ a≃0 =
        ⊥-elim (≄-derive a≃0)
      *-cancelᴸ {a} {b} {c} ab≃ac | ∨-introᴿ b-c≃0 =
        begin
          b
        ≃˘⟨ +-identityᴿ ⟩
          b + 0
        ≃˘⟨ AA.substᴿ +-inverseᴸ ⟩
          b + (- c + c)
        ≃˘⟨ AA.assoc ⟩
          b - c + c
        ≃⟨ AA.substᴸ b-c≃0 ⟩
          0 + c
        ≃⟨ +-identityᴸ ⟩
          c
        ∎

  *-cancellativeᴿ : AA.Cancellativeᴿ {A = ℤ} _*_
  *-cancellativeᴿ = AA.cancellativeᴿ
