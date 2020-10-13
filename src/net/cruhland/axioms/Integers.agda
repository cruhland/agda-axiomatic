open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.axioms.Integers (PA : PeanoArithmetic) where

open import Agda.Builtin.FromNat using (Number)
import Agda.Builtin.Nat as Nat
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import net.cruhland.models.Logic using (⊤; ¬_)
open PeanoArithmetic PA using (ℕ) renaming (_+_ to _+ᴺ_; number to ℕ-number)

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

infixl 6 _+_
_+_ : ℤ → ℤ → ℤ
a⁺ — a⁻ + b⁺ — b⁻ = (a⁺ +ᴺ b⁺) — (a⁻ +ᴺ b⁻)

fromNat : Nat.Nat → {{_ : ⊤}} → ℤ
fromNat Nat.zero = 0 — 0
fromNat (Nat.suc n) = 1 — 0 + fromNat n

instance
  number : Number ℤ
  number = record { Constraint = const ⊤ ; fromNat = fromNat }
