open import net.cruhland.axioms.Peano using (PeanoArithmetic)

module net.cruhland.models.Integers (PA : PeanoArithmetic) where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
import Agda.Builtin.Nat as Nat
open import Function using (_∘_; const; flip)
open import net.cruhland.axioms.DecEq using (DecEq)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; _≄ⁱ_; ≄ⁱ-elim; Eq; sym; ¬sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.models.Logic using
  (⊤; ∧-elimᴿ; _∨_; ∨-introᴸ; ∨-introᴿ; ⊥-elim; ¬_; Dec; yes; no)
module ℕ = PeanoArithmetic PA
open ℕ using (ℕ; _<⁺_) renaming
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

transpose : ∀ {w x y z} → (w +ᴺ x) +ᴺ (y +ᴺ z) ≃ (w +ᴺ y) +ᴺ (x +ᴺ z)
transpose {w} {x} {y} {z} =
  begin
    (w +ᴺ x) +ᴺ (y +ᴺ z)
  ≃⟨ [ab][cd]≃a[[bc]d] {w} ⟩
    w +ᴺ ((x +ᴺ y) +ᴺ z)
  ≃⟨ swap-middle {w} {x} ⟩
    w +ᴺ ((y +ᴺ x) +ᴺ z)
  ≃˘⟨ [ab][cd]≃a[[bc]d] {w} ⟩
    (w +ᴺ y) +ᴺ (x +ᴺ z)
  ∎

distrib-twoᴸ :
  ∀ {a b c d e f} →
    a *ᴺ (b +ᴺ c) +ᴺ d *ᴺ (e +ᴺ f) ≃
      (a *ᴺ b +ᴺ a *ᴺ c) +ᴺ (d *ᴺ e +ᴺ d *ᴺ f)
distrib-twoᴸ {a} {b} {c} {d} {e} {f} =
  begin
    a *ᴺ (b +ᴺ c) +ᴺ d *ᴺ (e +ᴺ f)
  ≃⟨ +ᴺ-substᴸ (ℕ.*-distrib-+ᴸ {a}) ⟩
    (a *ᴺ b +ᴺ a *ᴺ c) +ᴺ d *ᴺ (e +ᴺ f)
  ≃⟨ +ᴺ-substᴿ (ℕ.*-distrib-+ᴸ {d}) ⟩
    (a *ᴺ b +ᴺ a *ᴺ c) +ᴺ (d *ᴺ e +ᴺ d *ᴺ f)
  ∎

distrib-twoᴿ :
  ∀ {a b c d e f} →
    (a +ᴺ b) *ᴺ c +ᴺ (d +ᴺ e) *ᴺ f ≃
      (a *ᴺ c +ᴺ b *ᴺ c) +ᴺ (d *ᴺ f +ᴺ e *ᴺ f)
distrib-twoᴿ {a} {b} {c} {d} {e} {f} =
  begin
    (a +ᴺ b) *ᴺ c +ᴺ (d +ᴺ e) *ᴺ f
  ≃⟨ +ᴺ-substᴸ (ℕ.*-distrib-+ᴿ {a}) ⟩
    (a *ᴺ c +ᴺ b *ᴺ c) +ᴺ (d +ᴺ e) *ᴺ f
  ≃⟨ +ᴺ-substᴿ (ℕ.*-distrib-+ᴿ {d}) ⟩
    (a *ᴺ c +ᴺ b *ᴺ c) +ᴺ (d *ᴺ f +ᴺ e *ᴺ f)
  ∎

infix 9 _—_
record ℤ : Set where
  constructor _—_
  field
    n⁺ n⁻ : ℕ

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

data _≄ᶻⁱ_ (a b : ℤ) : Set where
  instance ≃ᶻⁱ-intro : {{i : ℤ⁺ a +ᴺ ℤ⁻ b ≄ⁱ ℤ⁺ b +ᴺ ℤ⁻ a}} → a ≄ᶻⁱ b

≄ᶻⁱ-elim : ∀ {a b} {{i : a ≄ᶻⁱ b}} → ¬ (a ≃ᶻ b)
≄ᶻⁱ-elim {{≃ᶻⁱ-intro {{≄ⁱ-ℕ}}}} (≃ᶻ-intro {{≃-ℕ}}) = ≄ⁱ-elim {{i = ≄ⁱ-ℕ}} ≃-ℕ

instance
  eq : Eq ℤ
  eq = record
    { _≃_ = _≃ᶻ_
    ; refl = ≃ᶻ-refl
    ; sym = ≃ᶻ-sym
    ; trans = ≃ᶻ-trans
    ; _≄ⁱ_ = _≄ᶻⁱ_
    ; ≄ⁱ-elim = λ {{i}} → ≄ᶻⁱ-elim {{i}}
    }

infixl 6 _+_
_+_ : ℤ → ℤ → ℤ
a⁺ — a⁻ + b⁺ — b⁻ = (a⁺ +ᴺ b⁺) — (a⁻ +ᴺ b⁻)

+-comm : ∀ {a b} → a + b ≃ b + a
+-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        (a⁺ +ᴺ b⁺) +ᴺ (b⁻ +ᴺ a⁻)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-comm {a⁺}) ⟩
        (b⁺ +ᴺ a⁺) +ᴺ (b⁻ +ᴺ a⁻)
      ≃⟨ +ᴺ-substᴿ {b⁺ +ᴺ a⁺} (+ᴺ-comm {b⁻}) ⟩
        (b⁺ +ᴺ a⁺) +ᴺ (a⁻ +ᴺ b⁻)
      ∎

+-substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ + b ≃ a₂ + b
+-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁≃a₂ = ≃ᶻ-intro {{eq′}}
  where
    a₁⁺+a₂⁻≃a₂⁺+a₁⁻ = ≃ᶻ-elim a₁≃a₂
    eq′ =
      begin
        (a₁⁺ +ᴺ b⁺) +ᴺ (a₂⁻ +ᴺ b⁻)
      ≃⟨ transpose {a₁⁺} ⟩
        (a₁⁺ +ᴺ a₂⁻) +ᴺ (b⁺ +ᴺ b⁻)
      ≃⟨ +ᴺ-substᴸ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
        (a₂⁺ +ᴺ a₁⁻) +ᴺ (b⁺ +ᴺ b⁻)
      ≃⟨ transpose {a₂⁺} ⟩
        (a₂⁺ +ᴺ b⁺) +ᴺ (a₁⁻ +ᴺ b⁻)
      ∎

+-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a + b₁ ≃ a + b₂
+-substᴿ {a} {b₁} {b₂} b₁≃b₂ =
  begin
    a + b₁
  ≃⟨ +-comm {a} ⟩
    b₁ + a
  ≃⟨ +-substᴸ b₁≃b₂ ⟩
    b₂ + a
  ≃⟨ +-comm {b₂} ⟩
    a + b₂
  ∎

+-assoc : ∀ {x y z} → (x + y) + z ≃ x + (y + z)
+-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        ((x⁺ +ᴺ y⁺) +ᴺ z⁺) +ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))
      ≃⟨ +ᴺ-substᴸ (+ᴺ-assoc {x⁺}) ⟩
        (x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ (x⁻ +ᴺ (y⁻ +ᴺ z⁻))
      ≃˘⟨ +ᴺ-substᴿ {x⁺ +ᴺ (y⁺ +ᴺ z⁺)} (+ᴺ-assoc {x⁻}) ⟩
        (x⁺ +ᴺ (y⁺ +ᴺ z⁺)) +ᴺ ((x⁻ +ᴺ y⁻) +ᴺ z⁻)
      ∎

fromNat : Nat.Nat → {{_ : ⊤}} → ℤ
fromNat Nat.zero = 0 — 0
fromNat (Nat.suc n) = 1 — 0 + fromNat n

instance
  number : Number ℤ
  number = record { Constraint = const ⊤ ; fromNat = fromNat }

fromℕ : ℕ → ℤ
fromℕ n = n — 0

fromℕ-subst : ∀ {n₁ n₂} → n₁ ≃ n₂ → fromℕ n₁ ≃ fromℕ n₂
fromℕ-subst n₁≃n₂ = ≃ᶻ-intro {{+ᴺ-substᴸ n₁≃n₂}}

ℕ≃→ℤ≃ : ∀ {n m} → n ≃ m → fromℕ n ≃ fromℕ m
ℕ≃→ℤ≃ n≃m = ≃ᶻ-intro {{trans ℕ.+-zeroᴿ (trans n≃m (sym ℕ.+-zeroᴿ))}}

ℤ≃→ℕ≃ : ∀ {n} → fromℕ n ≃ 0 → n ≃ 0
ℤ≃→ℕ≃ {n} (≃ᶻ-intro {{n+0≃0+0}}) =
  begin
    n
  ≃˘⟨ ℕ.+-zeroᴿ ⟩
    n +ᴺ 0
  ≃⟨ n+0≃0+0 ⟩
    0 +ᴺ 0
  ≃⟨ ℕ.+-zeroᴸ ⟩
    0
  ∎

+ᴺ-to-+ : ∀ {n m} → fromℕ (n +ᴺ m) ≃ fromℕ n + fromℕ m
+ᴺ-to-+ = ≃ᶻ-intro {{ℕ.+-substᴿ ℕ.+-zeroᴸ}}

+-identityᴸ : ∀ {x} → 0 + x ≃ x
+-identityᴸ {x⁺ — x⁻} = ≃ᶻ-intro {{[0+x⁺]+x⁻≃x⁺+[0+x⁻]}}
  where
    [0+x⁺]+x⁻≃x⁺+[0+x⁻] =
      begin
        0 +ᴺ x⁺ +ᴺ x⁻
      ≃⟨ ℕ.+-substᴸ ℕ.+-comm ⟩
        x⁺ +ᴺ 0 +ᴺ x⁻
      ≃⟨ ℕ.+-assoc ⟩
        x⁺ +ᴺ (0 +ᴺ x⁻)
      ∎

+-identityᴿ : ∀ {x} → x + 0 ≃ x
+-identityᴿ {x} =
  begin
    x + 0
  ≃⟨ +-comm {x} ⟩
    0 + x
  ≃⟨ +-identityᴸ ⟩
    x
  ∎

infix 8 -_
-_ : ℤ → ℤ
- a — b = b — a

instance
  negative : Negative ℤ
  negative = record { Constraint = const ⊤ ; fromNeg = λ n → - fromNat n }

neg-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → - a₁ ≃ - a₂
neg-subst {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} a₁≃a₂ = ≃ᶻ-intro {{eq′}}
  where
    a₁⁺+a₂⁻≃a₂⁺+a₁⁻ = ≃ᶻ-elim a₁≃a₂
    eq′ =
      begin
        a₁⁻ +ᴺ a₂⁺
      ≃⟨ +ᴺ-comm {a₁⁻} ⟩
        a₂⁺ +ᴺ a₁⁻
      ≃˘⟨ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
        a₁⁺ +ᴺ a₂⁻
      ≃⟨ +ᴺ-comm {a₁⁺} ⟩
        a₂⁻ +ᴺ a₁⁺
      ∎

neg-involutive : ∀ {a} → - (- a) ≃ a
neg-involutive {a⁺ — a⁻} = ≃ᶻ-intro

+-inverseᴸ : ∀ {x} → - x + x ≃ 0
+-inverseᴸ {x⁺ — x⁻} = ≃ᶻ-intro {{[x⁻+x⁺]+0≃0+[x⁺+x⁻]}}
  where
    [x⁻+x⁺]+0≃0+[x⁺+x⁻] =
      begin
        (x⁻ +ᴺ x⁺) +ᴺ 0
      ≃⟨ ℕ.+-comm ⟩
        0 +ᴺ (x⁻ +ᴺ x⁺)
      ≃⟨ ℕ.+-substᴿ ℕ.+-comm ⟩
        0 +ᴺ (x⁺ +ᴺ x⁻)
      ∎

+-inverseᴿ : ∀ {x} → x + - x ≃ 0
+-inverseᴿ {x} =
  begin
    x + - x
  ≃⟨ +-comm {x} ⟩
    - x + x
  ≃⟨ +-inverseᴸ {x} ⟩
    0
  ∎

infixl 6 _-_
_-_ : ℤ → ℤ → ℤ
x - y = x + (- y)

sub-substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
sub-substᴸ = +-substᴸ

sub-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a - b₁ ≃ a - b₂
sub-substᴿ = +-substᴿ ∘ neg-subst

infixl 7 _*_
_*_ : ℤ → ℤ → ℤ
a⁺ — a⁻ * b⁺ — b⁻ = (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻) — (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺)

*-comm : ∀ {a b} → a * b ≃ b * a
*-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-substᴸ (ℕ.*-comm {a⁺})) ⟩
        (b⁺ *ᴺ a⁺ +ᴺ a⁻ *ᴺ b⁻) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-substᴿ {b⁺ *ᴺ a⁺} (ℕ.*-comm {a⁻})) ⟩
        (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (b⁺ *ᴺ a⁻ +ᴺ b⁻ *ᴺ a⁺)
      ≃⟨ +ᴺ-substᴿ {b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻} (+ᴺ-comm {b⁺ *ᴺ a⁻}) ⟩
        (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (b⁻ *ᴺ a⁺ +ᴺ b⁺ *ᴺ a⁻)
      ≃⟨ +ᴺ-substᴿ {b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻} (+ᴺ-substᴸ (ℕ.*-comm {b⁻})) ⟩
        (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (a⁺ *ᴺ b⁻ +ᴺ b⁺ *ᴺ a⁻)
      ≃⟨ +ᴺ-substᴿ {b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻} (+ᴺ-substᴿ (ℕ.*-comm {b⁺})) ⟩
        (b⁺ *ᴺ a⁺ +ᴺ b⁻ *ᴺ a⁻) +ᴺ (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺)
      ∎

*-substᴸ : ∀ {a₁ a₂ b} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
*-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁≃a₂ = ≃ᶻ-intro {{eq′}}
  where
    rearr :
      ∀ {u v w x y z} →
        (w *ᴺ u +ᴺ x *ᴺ v) +ᴺ (y *ᴺ v +ᴺ z *ᴺ u) ≃
          (w +ᴺ z) *ᴺ u +ᴺ (y +ᴺ x) *ᴺ v
    rearr {u} {v} {w} {x} {y} {z} =
      begin
        (w *ᴺ u +ᴺ x *ᴺ v) +ᴺ (y *ᴺ v +ᴺ z *ᴺ u)
      ≃⟨ perm-adcb {w *ᴺ u} ⟩
        (w *ᴺ u +ᴺ z *ᴺ u) +ᴺ (y *ᴺ v +ᴺ x *ᴺ v)
      ≃˘⟨ distrib-twoᴿ {a = w} {d = y} ⟩
        (w +ᴺ z) *ᴺ u +ᴺ (y +ᴺ x) *ᴺ v
      ∎

    a₁⁺a₂⁻≃a₂⁺a₁⁻ = ≃ᶻ-elim a₁≃a₂
    eq′ =
      begin
        (a₁⁺ *ᴺ b⁺ +ᴺ a₁⁻ *ᴺ b⁻) +ᴺ (a₂⁺ *ᴺ b⁻ +ᴺ a₂⁻ *ᴺ b⁺)
      ≃⟨ rearr {w = a₁⁺} {y = a₂⁺} ⟩
        (a₁⁺ +ᴺ a₂⁻) *ᴺ b⁺ +ᴺ (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁻
      ≃⟨ +ᴺ-substᴸ (ℕ.*-substᴸ a₁⁺a₂⁻≃a₂⁺a₁⁻) ⟩
        (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁺ +ᴺ (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁻
      ≃˘⟨ +ᴺ-substᴿ (ℕ.*-substᴸ a₁⁺a₂⁻≃a₂⁺a₁⁻) ⟩
        (a₂⁺ +ᴺ a₁⁻) *ᴺ b⁺ +ᴺ (a₁⁺ +ᴺ a₂⁻) *ᴺ b⁻
      ≃˘⟨ rearr {w = a₂⁺} {y = a₁⁺} ⟩
        (a₂⁺ *ᴺ b⁺ +ᴺ a₂⁻ *ᴺ b⁻) +ᴺ (a₁⁺ *ᴺ b⁻ +ᴺ a₁⁻ *ᴺ b⁺)
      ∎

*-substᴿ : ∀ {a b₁ b₂} → b₁ ≃ b₂ → a * b₁ ≃ a * b₂
*-substᴿ {a} {b₁} {b₂} b₁≃b₂ =
  begin
    a * b₁
  ≃⟨ *-comm {a} ⟩
    b₁ * a
  ≃⟨ *-substᴸ b₁≃b₂ ⟩
    b₂ * a
  ≃⟨ *-comm {b₂} ⟩
    a * b₂
  ∎

*ᴺ-to-* : ∀ {n m} → fromℕ (n *ᴺ m) ≃ fromℕ n * fromℕ m
*ᴺ-to-* {n} {m} = ≃ᶻ-intro {{nm+n0+0m≃nm+00+0}}
  where
    nm+n0+0m≃nm+00+0 =
      begin
        n *ᴺ m +ᴺ (n *ᴺ 0 +ᴺ 0 *ᴺ m)
      ≃⟨ ℕ.+-substᴿ (ℕ.+-substᴸ (ℕ.*-zeroᴿ {n})) ⟩
        n *ᴺ m +ᴺ (0 +ᴺ 0 *ᴺ m)
      ≃˘⟨ ℕ.+-substᴿ (ℕ.+-substᴸ ℕ.*-zeroᴸ) ⟩
        n *ᴺ m +ᴺ (0 *ᴺ 0 +ᴺ 0 *ᴺ m)
      ≃⟨ ℕ.+-substᴿ (ℕ.+-substᴿ ℕ.*-zeroᴸ) ⟩
        n *ᴺ m +ᴺ (0 *ᴺ 0 +ᴺ 0)
      ≃˘⟨ +ᴺ-assoc {n *ᴺ m} ⟩
        n *ᴺ m +ᴺ 0 *ᴺ 0 +ᴺ 0
      ∎

*-distrib-+ᴸ : ∀ {x y z} → x * (y + z) ≃ x * y + x * z
*-distrib-+ᴸ {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} =
    ≃ᶻ-intro {{a≃b+c≃d (refactor {x⁺} {x⁻}) (sym (refactor {x⁺} {x⁻}))}}
  where
    refactor :
      ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
        b₁ *ᴺ (a₁ +ᴺ a₃) +ᴺ b₂ *ᴺ (a₂ +ᴺ a₄) ≃
          (b₁ *ᴺ a₁ +ᴺ b₂ *ᴺ a₂) +ᴺ (b₁ *ᴺ a₃ +ᴺ b₂ *ᴺ a₄)
    refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
      begin
        b₁ *ᴺ (a₁ +ᴺ a₃) +ᴺ b₂ *ᴺ (a₂ +ᴺ a₄)
      ≃⟨ distrib-twoᴸ {a = b₁} {d = b₂} ⟩
        (b₁ *ᴺ a₁ +ᴺ b₁ *ᴺ a₃) +ᴺ (b₂ *ᴺ a₂ +ᴺ b₂ *ᴺ a₄)
      ≃⟨ transpose {b₁ *ᴺ a₁} ⟩
        (b₁ *ᴺ a₁ +ᴺ b₂ *ᴺ a₂) +ᴺ (b₁ *ᴺ a₃ +ᴺ b₂ *ᴺ a₄)
      ∎

*-distrib-+ᴿ : ∀ {x y z} → (y + z) * x ≃ y * x + z * x
*-distrib-+ᴿ {x} {y} {z} =
  begin
    (y + z) * x
  ≃⟨ *-comm {y + z} ⟩
    x * (y + z)
  ≃⟨ *-distrib-+ᴸ {x} ⟩
    x * y + x * z
  ≃⟨ +-substᴸ (*-comm {x}) ⟩
    y * x + x * z
  ≃⟨ +-substᴿ {y * x} (*-comm {x}) ⟩
    y * x + z * x
  ∎

*-assoc : ∀ {x y z} → (x * y) * z ≃ x * (y * z)
*-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro {{eq′}}
  where
    assoc-four :
      ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃} →
        ((a₁ *ᴺ a₂) *ᴺ a₃ +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃) ≃
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ d₁ *ᴺ (d₂ *ᴺ d₃))
    assoc-four {a₁} {a₂} {a₃} {b₁} {b₂} {b₃} {c₁} {c₂} {c₃} {d₁} {d₂} {d₃} =
      begin
        ((a₁ *ᴺ a₂) *ᴺ a₃ +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-substᴸ (ℕ.*-assoc {a₁})) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ (b₁ *ᴺ b₂) *ᴺ b₃) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-substᴿ {a₁ *ᴺ (a₂ *ᴺ a₃)} (ℕ.*-assoc {b₁})) ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        ((c₁ *ᴺ c₂) *ᴺ c₃ +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴿ
           {(a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃))}
           (+ᴺ-substᴸ (ℕ.*-assoc {c₁}))
       ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ (d₁ *ᴺ d₂) *ᴺ d₃)
      ≃⟨ +ᴺ-substᴿ
           {(a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃))}
           (+ᴺ-substᴿ (ℕ.*-assoc {d₁}))
       ⟩
        (a₁ *ᴺ (a₂ *ᴺ a₃) +ᴺ b₁ *ᴺ (b₂ *ᴺ b₃)) +ᴺ
        (c₁ *ᴺ (c₂ *ᴺ c₃) +ᴺ d₁ *ᴺ (d₂ *ᴺ d₃))
      ∎

    refactor :
      ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
        (a₁ *ᴺ a₃ +ᴺ a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄ +ᴺ a₂ *ᴺ a₃) *ᴺ b₂ ≃
          a₁ *ᴺ (a₃ *ᴺ b₁ +ᴺ a₄ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₃ *ᴺ b₂ +ᴺ a₄ *ᴺ b₁)
    refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
      begin
        (a₁ *ᴺ a₃ +ᴺ a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄ +ᴺ a₂ *ᴺ a₃) *ᴺ b₂
      ≃⟨ distrib-twoᴿ {a = a₁ *ᴺ a₃} {d = a₁ *ᴺ a₄} ⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₂ *ᴺ a₄) *ᴺ b₁) +ᴺ
        ((a₁ *ᴺ a₄) *ᴺ b₂ +ᴺ (a₂ *ᴺ a₃) *ᴺ b₂)
      ≃⟨ transpose {(a₁ *ᴺ a₃) *ᴺ b₁}⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂) +ᴺ
        ((a₂ *ᴺ a₄) *ᴺ b₁ +ᴺ (a₂ *ᴺ a₃) *ᴺ b₂)
      ≃⟨ +ᴺ-substᴿ
           {(a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂}
           (+ᴺ-comm {(a₂ *ᴺ a₄) *ᴺ b₁})
       ⟩
        ((a₁ *ᴺ a₃) *ᴺ b₁ +ᴺ (a₁ *ᴺ a₄) *ᴺ b₂) +ᴺ
        ((a₂ *ᴺ a₃) *ᴺ b₂ +ᴺ (a₂ *ᴺ a₄) *ᴺ b₁)
      ≃⟨ assoc-four {a₁ = a₁} {b₁ = a₁} {c₁ = a₂} {d₁ = a₂} ⟩
        (a₁ *ᴺ (a₃ *ᴺ b₁) +ᴺ a₁ *ᴺ (a₄ *ᴺ b₂)) +ᴺ
        (a₂ *ᴺ (a₃ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₄ *ᴺ b₁))
      ≃˘⟨ distrib-twoᴸ {a = a₁} {d = a₂} ⟩
        a₁ *ᴺ (a₃ *ᴺ b₁ +ᴺ a₄ *ᴺ b₂) +ᴺ a₂ *ᴺ (a₃ *ᴺ b₂ +ᴺ a₄ *ᴺ b₁)
      ∎

    eq′ = a≃b+c≃d
           (refactor {z⁺} {z⁻} {x⁺} {x⁻})
           (sym (refactor {z⁻} {z⁺} {x⁺} {x⁻}))

*-negᴸ : ∀ {a b} → - a * b ≃ - (a * b)
*-negᴸ {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro {{eq′}}
  where
    eq′ =
      begin
        (a⁻ *ᴺ b⁺ +ᴺ a⁺ *ᴺ b⁻) +ᴺ (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻)
      ≃⟨ +ᴺ-substᴸ (+ᴺ-comm {a⁻ *ᴺ b⁺}) ⟩
        (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺) +ᴺ (a⁺ *ᴺ b⁺ +ᴺ a⁻ *ᴺ b⁻)
      ≃⟨ +ᴺ-substᴿ {a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺} (+ᴺ-comm {a⁺ *ᴺ b⁺}) ⟩
        (a⁺ *ᴺ b⁻ +ᴺ a⁻ *ᴺ b⁺) +ᴺ (a⁻ *ᴺ b⁻ +ᴺ a⁺ *ᴺ b⁺)
      ∎

*-negᴿ : ∀ {a b} → a * - b ≃ - (a * b)
*-negᴿ {a} {b} =
  begin
    a * - b
  ≃⟨ *-comm {a} ⟩
    - b * a
  ≃⟨ *-negᴸ {b} ⟩
    - (b * a)
  ≃⟨ neg-subst (*-comm {b}) ⟩
    - (a * b)
  ∎

neg-mult : ∀ {a} → - a ≃ -1 * a
neg-mult {a⁺ — a⁻} = ≃ᶻ-intro {{a⁻+[[0+0]a⁻+[1+0]a⁺]≃[0+0]a⁺+[1+0]a⁻+a⁺}}
  where
    a⁻+[[0+0]a⁻+[1+0]a⁺]≃[0+0]a⁺+[1+0]a⁻+a⁺ =
      begin
        a⁻ +ᴺ ((0 +ᴺ 0) *ᴺ a⁻ +ᴺ (1 +ᴺ 0) *ᴺ a⁺)
      ≃⟨ ℕ.+-substᴿ (ℕ.+-substᴸ (ℕ.*-substᴸ ℕ.+-zeroᴸ)) ⟩
        a⁻ +ᴺ (0 *ᴺ a⁻ +ᴺ (1 +ᴺ 0) *ᴺ a⁺)
      ≃⟨ ℕ.+-substᴿ (ℕ.+-substᴸ ℕ.*-zeroᴸ) ⟩
        a⁻ +ᴺ (0 +ᴺ (1 +ᴺ 0) *ᴺ a⁺)
      ≃⟨ ℕ.+-substᴿ ℕ.+-zeroᴸ ⟩
        a⁻ +ᴺ (1 +ᴺ 0) *ᴺ a⁺
      ≃⟨ ℕ.+-substᴿ (ℕ.*-substᴸ ℕ.+-zeroᴿ) ⟩
        a⁻ +ᴺ 1 *ᴺ a⁺
      ≃⟨ ℕ.+-substᴿ ℕ.*-oneᴸ ⟩
        a⁻ +ᴺ a⁺
      ≃˘⟨ ℕ.+-substᴸ ℕ.*-oneᴸ ⟩
        1 *ᴺ a⁻ +ᴺ a⁺
      ≃˘⟨ ℕ.+-substᴸ (ℕ.*-substᴸ ℕ.+-zeroᴿ) ⟩
        (1 +ᴺ 0) *ᴺ a⁻ +ᴺ a⁺
      ≃˘⟨ ℕ.+-zeroᴸ ⟩
        0 +ᴺ ((1 +ᴺ 0) *ᴺ a⁻ +ᴺ a⁺)
      ≃˘⟨ ℕ.+-substᴸ ℕ.*-zeroᴸ ⟩
        0 *ᴺ a⁺ +ᴺ ((1 +ᴺ 0) *ᴺ a⁻ +ᴺ a⁺)
      ≃˘⟨ ℕ.+-substᴸ (ℕ.*-substᴸ ℕ.+-zeroᴸ) ⟩
        (0 +ᴺ 0) *ᴺ a⁺ +ᴺ ((1 +ᴺ 0) *ᴺ a⁻ +ᴺ a⁺)
      ≃˘⟨ ℕ.+-assoc ⟩
        (0 +ᴺ 0) *ᴺ a⁺ +ᴺ (1 +ᴺ 0) *ᴺ a⁻ +ᴺ a⁺
      ∎

*-distrib-subᴸ : ∀ {a b c} → c * (a - b) ≃ c * a - c * b
*-distrib-subᴸ {a} {b} {c} =
  begin
    c * (a - b)
  ≃⟨⟩
    c * (a + - b)
  ≃⟨ *-distrib-+ᴸ {c} ⟩
    c * a + c * - b
  ≃⟨ +-substᴿ {c * a} (*-negᴿ {c}) ⟩
    c * a + - (c * b)
  ≃⟨⟩
    c * a - c * b
  ∎

*-distrib-subᴿ : ∀ {a b c} → (a - b) * c ≃ a * c - b * c
*-distrib-subᴿ {a} {b} {c} =
  begin
    (a - b) * c
  ≃⟨⟩
    (a + - b) * c
  ≃⟨ *-distrib-+ᴿ {c} {a} ⟩
    a * c + (- b) * c
  ≃⟨ +-substᴿ {a * c} (*-negᴸ {b}) ⟩
    a * c + - (b * c)
  ≃⟨⟩
    a * c - b * c
  ∎

*-zeroᴸ : ∀ {x} → 0 * x ≃ 0
*-zeroᴸ {x} =
  begin
    0 * x
  ≃˘⟨ *-substᴸ +-inverseᴿ ⟩
    (1 - 1) * x
  ≃⟨ *-distrib-subᴿ ⟩
    1 * x - 1 * x
  ≃⟨ +-inverseᴿ ⟩
    0
  ∎

neg-sub-swap : ∀ {a b} → - (a - b) ≃ b - a
neg-sub-swap {a} {b} =
  begin
    - (a - b)
  ≃⟨ neg-mult ⟩
    -1 * (a - b)
  ≃⟨ *-distrib-subᴸ {a} {b} { -1} ⟩
    -1 * a - -1 * b
  ≃˘⟨ +-substᴸ (neg-mult {a}) ⟩
    - a - -1 * b
  ≃˘⟨ +-substᴿ (neg-subst (neg-mult {b})) ⟩
    - a - (- b)
  ≃⟨ +-substᴿ (neg-involutive {b}) ⟩
    - a + b
  ≃˘⟨ +-comm {b} ⟩
    b - a
  ∎

≃ᴸ-subᴿ-toᴸ : ∀ {a b c} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ +-identityᴿ ⟩
    a + 0
  ≃˘⟨ +-substᴿ (+-inverseᴿ {b}) ⟩
    a + (b - b)
  ≃⟨ +-substᴿ {a} (+-comm {b}) ⟩
    a + (- b + b)
  ≃˘⟨ +-assoc {a} ⟩
    a - b + b
  ≃⟨ +-substᴸ a-b≃c ⟩
    c + b
  ≃⟨ +-comm {c} ⟩
    b + c
  ∎

record IsPositive (x : ℤ) : Set where
  field
    n : ℕ
    pos : ℕ.Positive n
    x≃n : x ≃ fromℕ n

record IsNegative (x : ℤ) : Set where
  field
    n : ℕ
    pos : ℕ.Positive n
    x≃-n : x ≃ - fromℕ n

data AtLeastOne (x : ℤ) : Set where
  nil : x ≃ 0 → AtLeastOne x
  pos : IsPositive x → AtLeastOne x
  neg : IsNegative x → AtLeastOne x

data MoreThanOne (x : ℤ) : Set where
  nil∧pos : x ≃ 0 → IsPositive x → MoreThanOne x
  nil∧neg : x ≃ 0 → IsNegative x → MoreThanOne x
  pos∧neg : IsPositive x → IsNegative x → MoreThanOne x

record Trichotomy (x : ℤ) : Set where
  field
    at-least : AtLeastOne x
    at-most : ¬ MoreThanOne x

open Trichotomy

trichotomy : ∀ x → Trichotomy x
trichotomy (x⁺ — x⁻) = record { at-least = one≤ ; at-most = one≮ }
  where
    one≤ : AtLeastOne (x⁺ — x⁻)
    one≤ with ℕ.trichotomy {x⁺} {x⁻}
    one≤ | ℕ.tri-< x⁺<x⁻ =
        let record { d = n ; d≄z = pos-n ; n+d≃m = x⁺+n≃x⁻ } = ℕ.<→<⁺ x⁺<x⁻
            x⁺+n≃0+x⁻ =
              begin
                x⁺ +ᴺ n
              ≃⟨ x⁺+n≃x⁻ ⟩
                x⁻
              ≃˘⟨ ℕ.+-zeroᴸ ⟩
                0 +ᴺ x⁻
              ∎
         in neg (record { n = n ; pos = pos-n ; x≃-n = ≃ᶻ-intro {{x⁺+n≃0+x⁻}} })
    one≤ | ℕ.tri-≃ x⁺≃x⁻ =
      nil (≃ᶻ-intro {{trans ℕ.+-zeroᴿ (trans x⁺≃x⁻ (sym ℕ.+-zeroᴸ))}})
    one≤ | ℕ.tri-> x⁺>x⁻ =
      let record { d = n ; d≄z = pos-n ; n+d≃m = x⁻+n≃x⁺ } = ℕ.<→<⁺ x⁺>x⁻
          x⁺—x⁻≃n =
            begin
              x⁺ +ᴺ 0
            ≃⟨ ℕ.+-zeroᴿ ⟩
              x⁺
            ≃˘⟨ x⁻+n≃x⁺ ⟩
              x⁻ +ᴺ n
            ≃⟨ +ᴺ-comm {x⁻} ⟩
              n +ᴺ x⁻
            ∎
       in pos (record { n = n ; pos = pos-n ; x≃n = ≃ᶻ-intro {{x⁺—x⁻≃n}} })

    one≮ : ¬ MoreThanOne (x⁺ — x⁻)
    one≮ (nil∧pos
            (≃ᶻ-intro {{x⁺+0≃x⁻}})
            record { n = n ; pos = n≄0 ; x≃n = ≃ᶻ-intro {{x⁺+0≃n+x⁻}} }) =
      let x⁻+n≃0+x⁻ = trans (+ᴺ-comm {x⁻}) (trans (sym x⁺+0≃n+x⁻) x⁺+0≃x⁻)
       in n≄0 (ℕ.+-unchanged (trans x⁻+n≃0+x⁻ ℕ.+-zeroᴸ))
    one≮ (nil∧neg
            (≃ᶻ-intro {{x⁺+0≃x⁻}})
            record { n = n ; pos = n≄0 ; x≃-n = ≃ᶻ-intro {{x⁺+n≃x⁻}} }) =
      n≄0 (ℕ.+-cancelᴸ (trans x⁺+n≃x⁻ (sym x⁺+0≃x⁻)))
    one≮ (pos∧neg
            record { n = n₁ ; pos = n₁≄0 ; x≃n = ≃ᶻ-intro {{x⁺+0≃n₁+x⁻}} }
            record { n = n₂ ; pos = n₂≄0 ; x≃-n = ≃ᶻ-intro {{x⁺+n₂≃0+x⁻}} }) =
      let x⁺+[n₂+n₁]≃x⁺+0 =
            begin
              x⁺ +ᴺ (n₂ +ᴺ n₁)
            ≃˘⟨ ℕ.+-assoc {x⁺} ⟩
              (x⁺ +ᴺ n₂) +ᴺ n₁
            ≃⟨ ℕ.+-substᴸ x⁺+n₂≃0+x⁻ ⟩
              (0 +ᴺ x⁻) +ᴺ n₁
            ≃⟨ ℕ.+-substᴸ ℕ.+-zeroᴸ ⟩
              x⁻ +ᴺ n₁
            ≃⟨ ℕ.+-comm {x⁻} ⟩
              n₁ +ᴺ x⁻
            ≃˘⟨ x⁺+0≃n₁+x⁻ ⟩
              x⁺ +ᴺ 0
            ∎
       in ℕ.+-positive n₂≄0 (ℕ.+-cancelᴸ x⁺+[n₂+n₁]≃x⁺+0)

*-either-zero : ∀ {a b} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
*-either-zero {a} {b} ab≃0 with at-least (trichotomy a)
*-either-zero {a} {b} ab≃0 | nil a≃0 =
  ∨-introᴸ a≃0
*-either-zero {a} {b⁺ — b⁻} ab≃0
    | pos record { n = n ; pos = n≄0 ; x≃n = a≃n—0 } =
  let nb≃0 = trans (*-substᴸ {b = b⁺ — b⁻} (sym a≃n—0)) ab≃0
      nb⁺+0b⁻+0≃0+[nb⁻+0b⁺] = ≃ᶻ-elim nb≃0
      nb⁺≃nb⁻ =
        begin
          n *ᴺ b⁺
        ≃˘⟨ ℕ.+-zeroᴿ ⟩
          n *ᴺ b⁺ +ᴺ 0
        ≃˘⟨ ℕ.+-substᴿ ℕ.*-zeroᴸ ⟩
          n *ᴺ b⁺ +ᴺ 0 *ᴺ b⁻
        ≃˘⟨ ℕ.+-zeroᴿ ⟩
          n *ᴺ b⁺ +ᴺ 0 *ᴺ b⁻ +ᴺ 0
        ≃⟨ nb⁺+0b⁻+0≃0+[nb⁻+0b⁺] ⟩
          0 +ᴺ (n *ᴺ b⁻ +ᴺ 0 *ᴺ b⁺)
        ≃⟨ ℕ.+-zeroᴸ ⟩
          n *ᴺ b⁻ +ᴺ 0 *ᴺ b⁺
        ≃⟨ ℕ.+-substᴿ ℕ.*-zeroᴸ ⟩
          n *ᴺ b⁻ +ᴺ 0
        ≃⟨ ℕ.+-zeroᴿ ⟩
          n *ᴺ b⁻
        ∎
      b⁺≃b⁻ = ℕ.*-cancelᴸ n≄0 nb⁺≃nb⁻
      b⁺+0≃0+b⁻ = trans ℕ.+-zeroᴿ (trans b⁺≃b⁻ (sym ℕ.+-zeroᴸ))
   in ∨-introᴿ (≃ᶻ-intro {{b⁺+0≃0+b⁻}})
*-either-zero {a} {b⁺ — b⁻} ab≃0
    | neg record { n = n ; pos = n≄0 ; x≃-n = a≃0—n } =
  let ab≃[0—n]b = *-substᴸ {b = b⁺ — b⁻} a≃0—n
      0≃-nb = trans (sym ab≃0) ab≃[0—n]b
      0+[0b⁻+nb⁺]≃0b⁺+nb⁻+0 = ≃ᶻ-elim 0≃-nb
      0+[0b⁻+nb⁺]≃0b⁺+nb⁻ = trans 0+[0b⁻+nb⁺]≃0b⁺+nb⁻+0 ℕ.+-zeroᴿ
      nb⁺≃nb⁻ =
        begin
          n *ᴺ b⁺
        ≃˘⟨ ℕ.+-zeroᴸ ⟩
          0 +ᴺ n *ᴺ b⁺
        ≃˘⟨ ℕ.+-substᴸ ℕ.*-zeroᴸ ⟩
          0 *ᴺ b⁻ +ᴺ n *ᴺ b⁺
        ≃˘⟨ ℕ.+-zeroᴸ ⟩
          0 +ᴺ (0 *ᴺ b⁻ +ᴺ n *ᴺ b⁺)
        ≃⟨ 0+[0b⁻+nb⁺]≃0b⁺+nb⁻+0 ⟩
          0 *ᴺ b⁺ +ᴺ n *ᴺ b⁻ +ᴺ 0
        ≃⟨ ℕ.+-zeroᴿ ⟩
          0 *ᴺ b⁺ +ᴺ n *ᴺ b⁻
        ≃⟨ ℕ.+-substᴸ ℕ.*-zeroᴸ ⟩
          0 +ᴺ n *ᴺ b⁻
        ≃⟨ ℕ.+-zeroᴸ ⟩
          n *ᴺ b⁻
        ∎
      b⁺≃b⁻ = ℕ.*-cancelᴸ n≄0 nb⁺≃nb⁻
      b⁺+0≃0+b⁻ = trans ℕ.+-zeroᴿ (trans b⁺≃b⁻ (sym ℕ.+-zeroᴸ))
   in ∨-introᴿ (≃ᶻ-intro {{b⁺+0≃0+b⁻}})

*-neither-zero : ∀ {a b} → a ≄ 0 → b ≄ 0 → a * b ≄ 0
*-neither-zero a≄0 b≄0 ab≃0 with *-either-zero ab≃0
... | ∨-introᴸ a≃0 = a≄0 a≃0
... | ∨-introᴿ b≃0 = b≄0 b≃0

*-cancelᴿ : ∀ {a b c} → c ≄ 0 → a * c ≃ b * c → a ≃ b
*-cancelᴿ {a} {b} {c} c≄0 ac≃bc with
  let [a-b]c≃0 =
        begin
          (a - b) * c
        ≃⟨ *-distrib-subᴿ {a} {b} ⟩
          a * c - b * c
        ≃⟨ sub-substᴸ {b = b * c} ac≃bc ⟩
          b * c - b * c
        ≃⟨ +-inverseᴿ {b * c} ⟩
          0
        ∎
   in *-either-zero {a - b} [a-b]c≃0
*-cancelᴿ {a} {b} {c} c≄0 ac≃bc | ∨-introᴸ a-b≃0 =
  begin
    a
  ≃˘⟨ +-identityᴿ ⟩
    a + 0
  ≃˘⟨ +-substᴿ {a} (+-inverseᴸ {b}) ⟩
    a + (- b + b)
  ≃˘⟨ +-assoc {a} ⟩
    a - b + b
  ≃⟨ +-substᴸ a-b≃0 ⟩
    0 + b
  ≃⟨ +-identityᴸ ⟩
    b
  ∎
*-cancelᴿ {a} {b} {c} c≄0 ac≃bc | ∨-introᴿ c≃0 =
  ⊥-elim (c≄0 c≃0)

infix 4 _≤_
record _≤_ (n m : ℤ) : Set where
  constructor ≤-intro
  field
    a : ℕ
    n≃m+a : m ≃ n + fromℕ a

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
  let n₁+ᴺn₂≃0 =
        begin
          fromℕ (n₁ +ᴺ n₂)
        ≃⟨ +ᴺ-to-+ {n₁} ⟩
          fromℕ n₁ + fromℕ n₂
        ≃˘⟨ +-identityᴸ ⟩
          0 + (fromℕ n₁ + fromℕ n₂)
        ≃˘⟨ +-substᴸ (+-inverseᴸ {a}) ⟩
          (- a) + a + (fromℕ n₁ + fromℕ n₂)
        ≃⟨ +-assoc { - a} ⟩
          (- a) + (a + (fromℕ n₁ + fromℕ n₂))
        ≃˘⟨ +-substᴿ { - a} (+-assoc {a}) ⟩
          (- a) + (a + fromℕ n₁ + fromℕ n₂)
        ≃˘⟨ +-substᴿ { - a} (+-substᴸ b≃a+n₁) ⟩
          (- a) + (b + fromℕ n₂)
        ≃˘⟨ +-substᴿ a≃b+n₂ ⟩
          (- a) + a
        ≃⟨ +-inverseᴸ {a} ⟩
          0
        ∎
      n₂≃0 = ∧-elimᴿ (ℕ.+-both-zero (ℤ≃→ℕ≃ n₁+ᴺn₂≃0))
   in trans (trans a≃b+n₂ (+-substᴿ (fromℕ-subst n₂≃0))) +-identityᴿ

sub-sign-swap : ∀ {a b} → IsNegative (a - b) → IsPositive (b - a)
sub-sign-swap {a} {b} record { n = n ; pos = n≄0 ; x≃-n = a-b≃-n } =
    record { n = n ; pos = n≄0 ; x≃n = b-a≃n }
  where
    b-a≃n =
      begin
        b - a
      ≃˘⟨ neg-sub-swap {a} ⟩
        - (a - b)
      ≃⟨ neg-subst a-b≃-n ⟩
        - (- fromℕ n)
      ≃⟨ neg-involutive {fromℕ n} ⟩
        fromℕ n
      ∎

pos→< : ∀ {x y} → IsPositive (y - x) → x < y
pos→< {x} {y} record { n = n ; pos = n≄0 ; x≃n = y-x≃n } =
    <-intro (≤-intro n (≃ᴸ-subᴿ-toᴸ y-x≃n)) x≄y
  where
    x≄y : x ≄ y
    x≄y x≃y = n≄0 (ℤ≃→ℕ≃ n≃0)
      where
        n≃0 =
          begin
            fromℕ n
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
    1≤ with at-least (trichotomy (b - a))
    1≤ | nil b-a≃0 = 2nd (sym (trans (≃ᴸ-subᴿ-toᴸ b-a≃0) +-identityᴿ))
    1≤ | pos b-a>0 = 1st (pos→< b-a>0)
    1≤ | neg b-a<0 = 3rd (pos→< (sub-sign-swap {b} b-a<0))

    ≤1 : ¬ TwoOfThree (a < b) (a ≃ b) (a > b)
    ≤1 (1∧2 (<-intro a≤b a≄b) a≃b) = a≄b a≃b
    ≤1 (1∧3 (<-intro a≤b a≄b) (<-intro b≤a b≄a)) = a≄b (≤-antisym a≤b b≤a)
    ≤1 (2∧3 a≃b (<-intro b≤a b≄a)) = b≄a (sym a≃b)

_≃?₀_ : (a b : ℤ) → Dec (a ≃ b)
a ≃?₀ b with at-least-one (order-trichotomy a b)
a ≃?₀ b | 1st (<-intro a≤b a≄b) = no a≄b
a ≃?₀ b | 2nd a≃b = yes a≃b
a ≃?₀ b | 3rd (<-intro b≤a b≄a) = no (¬sym b≄a)

instance
  decEq : DecEq ℤ
  decEq = record { _≃?_ = _≃?₀_ }
