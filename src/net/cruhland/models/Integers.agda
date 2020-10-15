open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers (PA : PeanoArithmetic) where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
import Agda.Builtin.Nat as Nat
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import net.cruhland.models.Logic using (⊤; ¬_)
open PeanoArithmetic PA using (ℕ) renaming
  (_+_ to _+ᴺ_; _*_ to _*ᴺ_; number to ℕ-number)

infix 9 _—_
data ℤ : Set where
  _—_ : ℕ → ℕ → ℤ

ℤ⁺ : ℤ → ℕ
ℤ⁺ (a⁺ — _) = a⁺

ℤ⁻ : ℤ → ℕ
ℤ⁻ (_ — a⁻) = a⁻

infix 4 _≃_
record _≃_ (a b : ℤ) : Set where
  constructor ≃-intro
  field
    ≃-elim : ℤ⁺ a +ᴺ ℤ⁻ b ≡ ℤ⁺ b +ᴺ ℤ⁻ a

infix 4 _≄_
_≄_ : ℤ → ℤ → Set
x ≄ y = ¬ (x ≃ y)

≃-refl : ∀ {a} → a ≃ a
≃-refl {a⁺ — a⁻} = ≃-intro refl

infixl 6 _+_
_+_ : ℤ → ℤ → ℤ
a⁺ — a⁻ + b⁺ — b⁻ = (a⁺ +ᴺ b⁺) — (a⁻ +ᴺ b⁻)

fromNat : Nat.Nat → {{_ : ⊤}} → ℤ
fromNat Nat.zero = 0 — 0
fromNat (Nat.suc n) = 1 — 0 + fromNat n

infix 8 -_
-_ : ℤ → ℤ
- a — b = b — a

instance
  number : Number ℤ
  number = record { Constraint = const ⊤ ; fromNat = fromNat }

  negative : Negative ℤ
  negative = record { Constraint = const ⊤ ; fromNeg = λ n → - fromNat n }

infixl 7 _*_
_*_ : ℤ → ℤ → ℤ
a⁺ — a⁻ * b⁺ — b⁻ = (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻) — (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺)
