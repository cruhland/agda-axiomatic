open import Relation.Nullary.Decidable using (False)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; DecEq; ≄-derive)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; ¬sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Function using (flip)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (⊤; ∧-elimᴿ; ∨-introᴸ; ∨-introᴿ; ⊥-elim; ¬_; Dec; no; yes)

module net.cruhland.models.Integers.Ordering (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
import net.cruhland.models.Integers.Addition PA as ℤ+
open import net.cruhland.models.Integers.Base PA as ℤ using (ℤ)
import net.cruhland.models.Integers.Equality PA as ℤ≃
import net.cruhland.models.Integers.Literals PA as ℤLit
import net.cruhland.models.Integers.Multiplication PA as ℤ*
import net.cruhland.models.Integers.Negation PA as ℤ-

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
        ≃⟨ AA.compat₂ ⟩
          (n₁ as ℤ) + (n₂ as ℤ)
        ≃˘⟨ AA.ident ⟩
          0 + ((n₁ as ℤ) + (n₂ as ℤ))
        ≃˘⟨ AA.subst AA.invᴸ ⟩
          (- a) + a + ((n₁ as ℤ) + (n₂ as ℤ))
        ≃⟨ AA.assoc ⟩
          (- a) + (a + ((n₁ as ℤ) + (n₂ as ℤ)))
        ≃˘⟨ AA.subst {f = - a +_} AA.assoc ⟩
          (- a) + (a + (n₁ as ℤ) + (n₂ as ℤ))
        ≃˘⟨ AA.subst {f = - a +_} (AA.subst b≃a+n₁) ⟩
          (- a) + (b + (n₂ as ℤ))
        ≃˘⟨ AA.subst a≃b+n₂ ⟩
          (- a) + a
        ≃⟨ AA.invᴸ ⟩
          0
        ∎
      n₂≃0 = ∧-elimᴿ (ℕ.+-both-zero (AA.inject n₁+n₂≃0))
   in begin
        a
      ≃⟨ a≃b+n₂ ⟩
        b + (n₂ as ℤ)
      ≃⟨ AA.subst {f = b +_} (AA.subst {_~_ = _≃_} {_≈_ = _≃_} n₂≃0) ⟩
        b + (0 as ℤ)
      ≃⟨ AA.ident ⟩
        b
      ∎

pos→< : ∀ {x y} → ℤ-.Positive (y - x) → x < y
pos→< {x} {y} record { n = n ; pos = n≄0 ; x≃n = y-x≃n } =
    <-intro (≤-intro n (ℤ-.≃ᴸ-subᴿ-toᴸ y-x≃n)) x≄y
  where
    x≄y : x ≄ y
    x≄y x≃y = n≄0 (AA.inject n≃0)
      where
        n≃0 =
          begin
            (n as ℤ)
          ≃˘⟨ y-x≃n ⟩
            y - x
          ≃⟨ ℤ-.sub-substᴿ x≃y ⟩
            y - y
          ≃⟨ AA.invᴿ ⟩
            0
          ∎

order-trichotomy : ∀ a b → AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b)
order-trichotomy a b = record { at-least-one = 1≤ ; at-most-one = ≤1 }
  where
    1≤ : AA.OneOfThree (a < b) (a ≃ b) (a > b)
    1≤ with AA.ExactlyOneOfThree.at-least-one (ℤ-.trichotomy (b - a))
    1≤ | AA.2nd b-a≃0 = AA.2nd (sym (trans (ℤ-.≃ᴸ-subᴿ-toᴸ b-a≃0) AA.ident))
    1≤ | AA.3rd b-a>0 = AA.1st (pos→< b-a>0)
    1≤ | AA.1st b-a<0 = AA.3rd (pos→< (ℤ*.sub-sign-swap {b} b-a<0))

    ≤1 : ¬ AA.TwoOfThree (a < b) (a ≃ b) (a > b)
    ≤1 (AA.1∧2 (<-intro a≤b a≄b) a≃b) = a≄b a≃b
    ≤1 (AA.1∧3 (<-intro a≤b a≄b) (<-intro b≤a b≄a)) = a≄b (≤-antisym a≤b b≤a)
    ≤1 (AA.2∧3 a≃b (<-intro b≤a b≄a)) = b≄a (sym a≃b)

instance
  decEq : DecEq ℤ
  decEq = record { Constraint = λ _ _ → ⊤ ; _≃?_ = _≃?₀_ }
    where
      _≃?₀_ : (a b : ℤ) {{_ : ⊤}} → Dec (a ≃ b)
      a ≃?₀ b with AA.ExactlyOneOfThree.at-least-one (order-trichotomy a b)
      a ≃?₀ b | AA.1st (<-intro a≤b a≄b) = no a≄b
      a ≃?₀ b | AA.2nd a≃b = yes a≃b
      a ≃?₀ b | AA.3rd (<-intro b≤a b≄a) = no (¬sym b≄a)

  *-cancellativeᴸ : AA.Cancellativeᴸ _*_ _≃_
  *-cancellativeᴸ = AA.cancellativeⁱᴸ Constraint *-cancelᴸ
    where
      Constraint = λ a → False (a ≃? 0)

      *-cancelᴸ : {a b c : ℤ} {{_ : Constraint a}} → a * b ≃ a * c → b ≃ c
      *-cancelᴸ {a} {b} {c} ab≃ac with
        let a[b-c]≃0 =
              begin
                a * (b - c)
              ≃⟨ ℤ*.*-distrib-subᴸ ⟩
                a * b - a * c
              ≃⟨ ℤ-.sub-substᴸ ab≃ac ⟩
                a * c - a * c
              ≃⟨ AA.invᴿ ⟩
                0
              ∎
         in AA.zero-prod a[b-c]≃0
      *-cancelᴸ {a} {b} {c} ab≃ac | ∨-introᴸ a≃0 =
        ⊥-elim (≄-derive a≃0)
      *-cancelᴸ {a} {b} {c} ab≃ac | ∨-introᴿ b-c≃0 =
        begin
          b
        ≃˘⟨ AA.ident ⟩
          b + 0
        ≃˘⟨ AA.subst AA.invᴸ ⟩
          b + (- c + c)
        ≃˘⟨ AA.assoc ⟩
          b - c + c
        ≃⟨ AA.subst b-c≃0 ⟩
          0 + c
        ≃⟨ AA.ident ⟩
          c
        ∎

  *-cancellativeᴿ : AA.Cancellativeᴿ {A = ℤ} _*_ _≃_
  *-cancellativeᴿ = AA.cancellativeᴿ-from-cancellativeᴸ
