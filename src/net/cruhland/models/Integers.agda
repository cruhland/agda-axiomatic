open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers (PA : PeanoArithmetic) where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
import Agda.Builtin.Nat as Nat
open import Function using (const)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; Eq; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.models.Logic using (⊤; ¬_)
open PeanoArithmetic PA using (ℕ) renaming
  ( _+_ to _+ᴺ_; +-assoc to +ᴺ-assoc; +-cancelᴿ to +ᴺ-cancelᴿ
  ; +-comm to +ᴺ-comm; +-substᴸ to +ᴺ-substᴸ; +-substᴿ to +ᴺ-substᴿ
  ; _*_ to _*ᴺ_; number to ℕ-number
  )

[ab][cd]≃a[[bc]d] : ∀ {a b c d} → (a +ᴺ b) +ᴺ (c +ᴺ d) ≃ a +ᴺ ((b +ᴺ c) +ᴺ d)
[ab][cd]≃a[[bc]d] {a} {b} {c} {d} =
  begin
    (a +ᴺ b) +ᴺ (c +ᴺ d)
  ≃⟨ +ᴺ-assoc {a} ⟩
    a +ᴺ (b +ᴺ (c +ᴺ d))
  ≃˘⟨ +ᴺ-substᴿ (+ᴺ-assoc {b}) ⟩
    a +ᴺ ((b +ᴺ c) +ᴺ d)
  ∎

swap-middle : ∀ {a b c d} → a +ᴺ ((b +ᴺ c) +ᴺ d) ≃ a +ᴺ ((c +ᴺ b) +ᴺ d)
swap-middle {a} {b} {c} {d} = +ᴺ-substᴿ (+ᴺ-substᴸ (+ᴺ-comm {b}))

regroup : ∀ a b c d → (a +ᴺ b) +ᴺ (c +ᴺ d) ≃ a +ᴺ ((b +ᴺ d) +ᴺ c)
regroup a b c d =
  begin
    (a +ᴺ b) +ᴺ (c +ᴺ d)
  ≃⟨ +ᴺ-substᴿ (+ᴺ-comm {c} {d}) ⟩
    (a +ᴺ b) +ᴺ (d +ᴺ c)
  ≃⟨ [ab][cd]≃a[[bc]d] {a} ⟩
    a +ᴺ ((b +ᴺ d) +ᴺ c)
  ∎

a≃b+c≃d : ∀ {a b c d} → a ≃ b → c ≃ d → a +ᴺ c ≃ b +ᴺ d
a≃b+c≃d {b = b} {c = c} a≃b c≃d = trans (+ᴺ-substᴸ a≃b) (+ᴺ-substᴿ c≃d)

perm-adcb : ∀ {a b c d} → (a +ᴺ d) +ᴺ (c +ᴺ b) ≃ (a +ᴺ b) +ᴺ (c +ᴺ d)
perm-adcb {a} {b} {c} {d} =
  begin
    (a +ᴺ d) +ᴺ (c +ᴺ b)
  ≃⟨ regroup a d c b ⟩
    a +ᴺ ((d +ᴺ b) +ᴺ c)
  ≃⟨ swap-middle {a} {d} ⟩
    a +ᴺ ((b +ᴺ d) +ᴺ c)
  ≃˘⟨ regroup a b c d ⟩
    (a +ᴺ b) +ᴺ (c +ᴺ d)
  ∎

infix 9 _—_
data ℤ : Set where
  _—_ : ℕ → ℕ → ℤ

ℤ⁺ : ℤ → ℕ
ℤ⁺ (a⁺ — _) = a⁺

ℤ⁻ : ℤ → ℕ
ℤ⁻ (_ — a⁻) = a⁻

record _≃ᶻ_ (a b : ℤ) : Set where
  instance constructor ≃ᶻ-intro
  field
    {{≃ᶻ-elim}} : ℤ⁺ a +ᴺ ℤ⁻ b ≃ ℤ⁺ b +ᴺ ℤ⁻ a

open _≃ᶻ_ public using (≃ᶻ-elim)

≃ᶻ-refl : ∀ {a} → a ≃ᶻ a
≃ᶻ-refl {a⁺ — a⁻} = ≃ᶻ-intro

≃ᶻ-sym : ∀ {a b} → a ≃ᶻ b → b ≃ᶻ a
≃ᶻ-sym {a⁺ — a⁻} {b⁺ — b⁻} (≃ᶻ-intro {{eq}}) = ≃ᶻ-intro {{sym eq}}

≃ᶻ-trans : ∀ {a b c} → a ≃ᶻ b → b ≃ᶻ c → a ≃ᶻ c
≃ᶻ-trans
  {a⁺ — a⁻} {b⁺ — b⁻} {c⁺ — c⁻}
  (≃ᶻ-intro {{a⁺+b⁻≃b⁺+a⁻}}) (≃ᶻ-intro {{b⁺+c⁻≃c⁺+b⁻}}) =
    ≃ᶻ-intro {{+ᴺ-cancelᴿ [a⁺+c⁻]+[b⁺+b⁻]≃[c⁺+a⁻]+[b⁺+b⁻]}}
  where
    [a⁺+c⁻]+[b⁺+b⁻]≃[c⁺+a⁻]+[b⁺+b⁻] =
      begin
        (a⁺ +ᴺ c⁻) +ᴺ (b⁺ +ᴺ b⁻)
      ≃˘⟨ perm-adcb {a⁺} ⟩
        (a⁺ +ᴺ b⁻) +ᴺ (b⁺ +ᴺ c⁻)
      ≃⟨ a≃b+c≃d a⁺+b⁻≃b⁺+a⁻ b⁺+c⁻≃c⁺+b⁻ ⟩
        (b⁺ +ᴺ a⁻) +ᴺ (c⁺ +ᴺ b⁻)
      ≃⟨ perm-adcb {b⁺} ⟩
        (b⁺ +ᴺ b⁻) +ᴺ (c⁺ +ᴺ a⁻)
      ≃⟨ +ᴺ-comm {n = b⁺ +ᴺ b⁻} ⟩
        (c⁺ +ᴺ a⁻) +ᴺ (b⁺ +ᴺ b⁻)
      ∎

instance
  eq : Eq ℤ
  eq = record { _≃_ = _≃ᶻ_ ; refl = ≃ᶻ-refl ; sym = ≃ᶻ-sym ; trans = ≃ᶻ-trans }

open Eq eq using (_≃_) public

infixl 6 _+_
_+_ : ℤ → ℤ → ℤ
a⁺ — a⁻ + b⁺ — b⁻ = (a⁺ +ᴺ b⁺) — (a⁻ +ᴺ b⁻)

fromNat : Nat.Nat → {{_ : ⊤}} → ℤ
fromNat Nat.zero = 0 — 0
fromNat (Nat.suc n) = 1 — 0 + fromNat n

fromℕ : ℕ → ℤ
fromℕ n = n — 0

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
