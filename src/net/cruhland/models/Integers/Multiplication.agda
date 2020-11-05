-- Needed for positive integer literals
import Agda.Builtin.FromNat as FromNat
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using (_≃_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; _*_; StarOp)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
-- Needed for instance of ⊤
open import net.cruhland.models.Logic using (_∨_; ∨-introᴸ; ∨-introᴿ)

module net.cruhland.models.Integers.Multiplication (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
import net.cruhland.models.Integers.Addition PA as Addition
open Addition using (+-comm; fromℕ; +-substᴸ; +-substᴿ)
open import net.cruhland.models.Integers.Base PA using (_—_; ℤ)
import net.cruhland.models.Integers.Equality PA as Equality
open Equality using (≃ᶻ-elim; ≃ᶻ-intro)
import net.cruhland.models.Integers.Negation PA as Negation
open Negation using
  ( -_; _-_; +-inverseᴿ; IsNegative; IsPositive; neg-involutive
  ; neg-subst; neg; nil; pos; Trichotomy; trichotomy
  )

instance
  star : StarOp ℤ
  star = record { _*_ = _*₀_ }
    where
      infixl 7 _*₀_
      _*₀_ : ℤ → ℤ → ℤ
      a⁺ — a⁻ *₀ b⁺ — b⁻ = (a⁺ * b⁺ + a⁻ * b⁻) — (a⁺ * b⁻ + a⁻ * b⁺)

  *-commutative : AA.Commutative _*_
  *-commutative = record { comm = *-comm }
    where
      *-comm : {a b : ℤ} → a * b ≃ b * a
      *-comm {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro eq′
        where
          eq′ =
            begin
              (a⁺ * b⁺ + a⁻ * b⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
            ≃⟨ AA.substᴸ (AA.substᴸ AA.comm) ⟩
              (b⁺ * a⁺ + a⁻ * b⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
            ≃⟨ AA.substᴸ (AA.substᴿ AA.comm) ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (b⁺ * a⁻ + b⁻ * a⁺)
            ≃⟨ AA.substᴿ AA.comm ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (b⁻ * a⁺ + b⁺ * a⁻)
            ≃⟨ AA.substᴿ (AA.substᴸ AA.comm) ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (a⁺ * b⁻ + b⁺ * a⁻)
            ≃⟨ AA.substᴿ (AA.substᴿ AA.comm) ⟩
              (b⁺ * a⁺ + b⁻ * a⁻) + (a⁺ * b⁻ + a⁻ * b⁺)
            ∎

  *-substitutiveᴸ : AA.Substitutiveᴸ _*_
  *-substitutiveᴸ = record { substᴸ = *-substᴸ }
    where
      *-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ * b ≃ a₂ * b
      *-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} a₁≃a₂ = ≃ᶻ-intro eq′
        where
          rearr :
            ∀ {u v w x y z} →
              (w * u + x * v) + (y * v + z * u) ≃
                (w + z) * u + (y + x) * v
          rearr {u} {v} {w} {x} {y} {z} =
            begin
              (w * u + x * v) + (y * v + z * u)
            ≃⟨ AA.perm-adcb ⟩
              (w * u + z * u) + (y * v + x * v)
            ≃˘⟨ AA.distrib-twoᴿ ⟩
              (w + z) * u + (y + x) * v
            ∎

          a₁⁺a₂⁻≃a₂⁺a₁⁻ = ≃ᶻ-elim a₁≃a₂
          eq′ =
            begin
              (a₁⁺ * b⁺ + a₁⁻ * b⁻) + (a₂⁺ * b⁻ + a₂⁻ * b⁺)
            ≃⟨ rearr {w = a₁⁺} {y = a₂⁺} ⟩
              (a₁⁺ + a₂⁻) * b⁺ + (a₂⁺ + a₁⁻) * b⁻
            ≃⟨ AA.substᴸ (AA.substᴸ a₁⁺a₂⁻≃a₂⁺a₁⁻) ⟩
              (a₂⁺ + a₁⁻) * b⁺ + (a₂⁺ + a₁⁻) * b⁻
            ≃˘⟨ AA.substᴿ (AA.substᴸ a₁⁺a₂⁻≃a₂⁺a₁⁻) ⟩
              (a₂⁺ + a₁⁻) * b⁺ + (a₁⁺ + a₂⁻) * b⁻
            ≃˘⟨ rearr {w = a₂⁺} {y = a₁⁺} ⟩
              (a₂⁺ * b⁺ + a₂⁻ * b⁻) + (a₁⁺ * b⁻ + a₁⁻ * b⁺)
            ∎

  *-substitutiveᴿ : AA.Substitutiveᴿ {A = ℤ} _*_
  *-substitutiveᴿ = AA.substitutiveᴿ

  *-substitutive₂ : AA.Substitutive₂ {A = ℤ} _*_
  *-substitutive₂ = AA.substitutive₂

*-to-* : ∀ {n m} → fromℕ (n * m) ≃ fromℕ n * fromℕ m
*-to-* {n} {m} = ≃ᶻ-intro nm+n0+0m≃nm+00+0
  where
    nm+n0+0m≃nm+00+0 =
      begin
        n * m + (n * 0 + 0 * m)
      ≃⟨ AA.substᴿ (AA.substᴸ (ℕ.*-zeroᴿ {n})) ⟩
        n * m + (0 + 0 * m)
      ≃˘⟨ AA.substᴿ (AA.substᴸ ℕ.*-zeroᴸ) ⟩
        n * m + (0 * 0 + 0 * m)
      ≃⟨ AA.substᴿ (AA.substᴿ ℕ.*-zeroᴸ) ⟩
        n * m + (0 * 0 + 0)
      ≃˘⟨ AA.assoc ⟩
        n * m + 0 * 0 + 0
      ∎

*-distrib-+ᴸ : {x y z : ℤ} → x * (y + z) ≃ x * y + x * z
*-distrib-+ᴸ {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} =
    ≃ᶻ-intro (AA.[a≃b][c≃d] (refactor {x⁺} {x⁻}) (sym (refactor {x⁺} {x⁻})))
  where
    refactor :
      ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
        b₁ * (a₁ + a₃) + b₂ * (a₂ + a₄) ≃
          (b₁ * a₁ + b₂ * a₂) + (b₁ * a₃ + b₂ * a₄)
    refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
      begin
        b₁ * (a₁ + a₃) + b₂ * (a₂ + a₄)
      ≃⟨ AA.distrib-twoᴸ ⟩
        (b₁ * a₁ + b₁ * a₃) + (b₂ * a₂ + b₂ * a₄)
      ≃⟨ AA.transpose ⟩
        (b₁ * a₁ + b₂ * a₂) + (b₁ * a₃ + b₂ * a₄)
      ∎

*-distrib-+ᴿ : ∀ {x y z} → (y + z) * x ≃ y * x + z * x
*-distrib-+ᴿ {x} {y} {z} =
  begin
    (y + z) * x
  ≃⟨ AA.comm ⟩
    x * (y + z)
  ≃⟨ *-distrib-+ᴸ {x} ⟩
    x * y + x * z
  ≃⟨ +-substᴸ AA.comm ⟩
    y * x + x * z
  ≃⟨ +-substᴿ {y * x} AA.comm ⟩
    y * x + z * x
  ∎

*-assoc : {x y z : ℤ} → (x * y) * z ≃ x * (y * z)
*-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro eq′
  where
    assoc-four :
      ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃} →
        ((a₁ * a₂) * a₃ + (b₁ * b₂) * b₃) +
        ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃) ≃
        (a₁ * (a₂ * a₃) + b₁ * (b₂ * b₃)) +
        (c₁ * (c₂ * c₃) + d₁ * (d₂ * d₃))
    assoc-four {a₁} {a₂} {a₃} {b₁} {b₂} {b₃} {c₁} {c₂} {c₃} {d₁} {d₂} {d₃} =
      begin
        ((a₁ * a₂) * a₃ + (b₁ * b₂) * b₃) +
        ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃)
      ≃⟨ AA.substᴸ (AA.substᴸ (ℕ.*-assoc {a₁})) ⟩
        (a₁ * (a₂ * a₃) + (b₁ * b₂) * b₃) +
        ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃)
      ≃⟨ AA.substᴸ (AA.substᴿ (ℕ.*-assoc {b₁})) ⟩
        (a₁ * (a₂ * a₃) + b₁ * (b₂ * b₃)) +
        ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃)
      ≃⟨ AA.substᴿ (AA.substᴸ (ℕ.*-assoc {c₁})) ⟩
        (a₁ * (a₂ * a₃) + b₁ * (b₂ * b₃)) +
        (c₁ * (c₂ * c₃) + (d₁ * d₂) * d₃)
      ≃⟨ AA.substᴿ (AA.substᴿ (ℕ.*-assoc {d₁})) ⟩
        (a₁ * (a₂ * a₃) + b₁ * (b₂ * b₃)) +
        (c₁ * (c₂ * c₃) + d₁ * (d₂ * d₃))
      ∎

    refactor :
      ∀ {b₁ b₂ a₁ a₂ a₃ a₄} →
        (a₁ * a₃ + a₂ * a₄) * b₁ + (a₁ * a₄ + a₂ * a₃) * b₂ ≃
          a₁ * (a₃ * b₁ + a₄ * b₂) + a₂ * (a₃ * b₂ + a₄ * b₁)
    refactor {b₁} {b₂} {a₁} {a₂} {a₃} {a₄} =
      begin
        (a₁ * a₃ + a₂ * a₄) * b₁ + (a₁ * a₄ + a₂ * a₃) * b₂
      ≃⟨ AA.distrib-twoᴿ ⟩
        ((a₁ * a₃) * b₁ + (a₂ * a₄) * b₁) +
        ((a₁ * a₄) * b₂ + (a₂ * a₃) * b₂)
      ≃⟨ AA.transpose ⟩
        ((a₁ * a₃) * b₁ + (a₁ * a₄) * b₂) +
        ((a₂ * a₄) * b₁ + (a₂ * a₃) * b₂)
      ≃⟨ AA.substᴿ AA.comm ⟩
        ((a₁ * a₃) * b₁ + (a₁ * a₄) * b₂) +
        ((a₂ * a₃) * b₂ + (a₂ * a₄) * b₁)
      ≃⟨ assoc-four {a₁ = a₁} {b₁ = a₁} {c₁ = a₂} {d₁ = a₂} ⟩
        (a₁ * (a₃ * b₁) + a₁ * (a₄ * b₂)) +
        (a₂ * (a₃ * b₂) + a₂ * (a₄ * b₁))
      ≃˘⟨ AA.distrib-twoᴸ ⟩
        a₁ * (a₃ * b₁ + a₄ * b₂) + a₂ * (a₃ * b₂ + a₄ * b₁)
      ∎

    eq′ = AA.[a≃b][c≃d]
           (refactor {z⁺} {z⁻} {x⁺} {x⁻})
           (sym (refactor {z⁻} {z⁺} {x⁺} {x⁻}))

instance
  *-associative : AA.Associative _*_
  *-associative = record { assoc = *-assoc }

*-negᴸ : ∀ {a b} → - a * b ≃ - (a * b)
*-negᴸ {a⁺ — a⁻} {b⁺ — b⁻} = ≃ᶻ-intro eq′
  where
    eq′ =
      begin
        (a⁻ * b⁺ + a⁺ * b⁻) + (a⁺ * b⁺ + a⁻ * b⁻)
      ≃⟨ AA.substᴸ AA.comm ⟩
        (a⁺ * b⁻ + a⁻ * b⁺) + (a⁺ * b⁺ + a⁻ * b⁻)
      ≃⟨ AA.substᴿ AA.comm ⟩
        (a⁺ * b⁻ + a⁻ * b⁺) + (a⁻ * b⁻ + a⁺ * b⁺)
      ∎

*-negᴿ : ∀ {a b} → a * - b ≃ - (a * b)
*-negᴿ {a} {b} =
  begin
    a * - b
  ≃⟨ AA.comm ⟩
    - b * a
  ≃⟨ *-negᴸ {b} ⟩
    - (b * a)
  ≃⟨ neg-subst AA.comm ⟩
    - (a * b)
  ∎

neg-mult : ∀ {a} → - a ≃ -1 * a
neg-mult {a⁺ — a⁻} = ≃ᶻ-intro a⁻+[[0+0]a⁻+[1+0]a⁺]≃[0+0]a⁺+[1+0]a⁻+a⁺
  where
    a⁻+[[0+0]a⁻+[1+0]a⁺]≃[0+0]a⁺+[1+0]a⁻+a⁺ =
      begin
        a⁻ + ((0 + 0) * a⁻ + (1 + 0) * a⁺)
      ≃⟨ AA.substᴿ (AA.substᴸ (AA.substᴸ AA.identᴸ)) ⟩
        a⁻ + (0 * a⁻ + (1 + 0) * a⁺)
      ≃⟨ AA.substᴿ (AA.substᴸ ℕ.*-zeroᴸ) ⟩
        a⁻ + (0 + (1 + 0) * a⁺)
      ≃⟨ AA.substᴿ AA.identᴸ ⟩
        a⁻ + (1 + 0) * a⁺
      ≃⟨ AA.substᴿ (AA.substᴸ AA.identᴿ) ⟩
        a⁻ + 1 * a⁺
      ≃⟨ AA.substᴿ ℕ.*-oneᴸ ⟩
        a⁻ + a⁺
      ≃˘⟨ AA.substᴸ ℕ.*-oneᴸ ⟩
        1 * a⁻ + a⁺
      ≃˘⟨ AA.substᴸ (AA.substᴸ AA.identᴿ) ⟩
        (1 + 0) * a⁻ + a⁺
      ≃˘⟨ AA.identᴸ ⟩
        0 + ((1 + 0) * a⁻ + a⁺)
      ≃˘⟨ AA.substᴸ ℕ.*-zeroᴸ ⟩
        0 * a⁺ + ((1 + 0) * a⁻ + a⁺)
      ≃˘⟨ AA.substᴸ (AA.substᴸ AA.identᴸ) ⟩
        (0 + 0) * a⁺ + ((1 + 0) * a⁻ + a⁺)
      ≃˘⟨ AA.assoc ⟩
        (0 + 0) * a⁺ + (1 + 0) * a⁻ + a⁺
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
  ≃˘⟨ AA.substᴸ +-inverseᴿ ⟩
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

instance
  zero-product : AA.ZeroProduct _*_ 0
  zero-product = record { zero-prod = *-either-zero }
    where
      *-either-zero : ∀ {a b} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
      *-either-zero {a} {b} ab≃0 with Trichotomy.at-least (trichotomy a)
      *-either-zero {a} {b} ab≃0 | nil a≃0 =
        ∨-introᴸ a≃0
      *-either-zero {a} {b⁺ — b⁻} ab≃0
          | pos record { n = n ; pos = n≄0 ; x≃n = a≃n—0 } =
        let nb≃0 = trans (AA.substᴸ {b = b⁺ — b⁻} (sym a≃n—0)) ab≃0
            nb⁺+0b⁻+0≃0+[nb⁻+0b⁺] = ≃ᶻ-elim nb≃0
            nb⁺≃nb⁻ =
              begin
                n * b⁺
              ≃˘⟨ AA.identᴿ ⟩
                n * b⁺ + 0
              ≃˘⟨ AA.substᴿ ℕ.*-zeroᴸ ⟩
                n * b⁺ + 0 * b⁻
              ≃˘⟨ AA.identᴿ ⟩
                n * b⁺ + 0 * b⁻ + 0
              ≃⟨ nb⁺+0b⁻+0≃0+[nb⁻+0b⁺] ⟩
                0 + (n * b⁻ + 0 * b⁺)
              ≃⟨ AA.identᴸ ⟩
                n * b⁻ + 0 * b⁺
              ≃⟨ AA.substᴿ ℕ.*-zeroᴸ ⟩
                n * b⁻ + 0
              ≃⟨ AA.identᴿ ⟩
                n * b⁻
              ∎
            b⁺≃b⁻ = AA.cancelᴸ {{c = fromWitnessFalse n≄0}} nb⁺≃nb⁻
            b⁺+0≃0+b⁻ = trans AA.identᴿ (trans b⁺≃b⁻ (sym AA.identᴸ))
         in ∨-introᴿ (≃ᶻ-intro b⁺+0≃0+b⁻)
      *-either-zero {a} {b⁺ — b⁻} ab≃0
          | neg record { n = n ; pos = n≄0 ; x≃-n = a≃0—n } =
        let ab≃[0—n]b = AA.substᴸ {b = b⁺ — b⁻} a≃0—n
            0≃-nb = trans (sym ab≃0) ab≃[0—n]b
            0+[0b⁻+nb⁺]≃0b⁺+nb⁻+0 = ≃ᶻ-elim 0≃-nb
            0+[0b⁻+nb⁺]≃0b⁺+nb⁻ = trans 0+[0b⁻+nb⁺]≃0b⁺+nb⁻+0 AA.identᴿ
            nb⁺≃nb⁻ =
              begin
                n * b⁺
              ≃˘⟨ AA.identᴸ ⟩
                0 + n * b⁺
              ≃˘⟨ AA.substᴸ ℕ.*-zeroᴸ ⟩
                0 * b⁻ + n * b⁺
              ≃˘⟨ AA.identᴸ ⟩
                0 + (0 * b⁻ + n * b⁺)
              ≃⟨ 0+[0b⁻+nb⁺]≃0b⁺+nb⁻+0 ⟩
                0 * b⁺ + n * b⁻ + 0
              ≃⟨ AA.identᴿ ⟩
                0 * b⁺ + n * b⁻
              ≃⟨ AA.substᴸ ℕ.*-zeroᴸ ⟩
                0 + n * b⁻
              ≃⟨ AA.identᴸ ⟩
                n * b⁻
              ∎
            b⁺≃b⁻ = AA.cancelᴸ {{c = fromWitnessFalse n≄0}} nb⁺≃nb⁻
            b⁺+0≃0+b⁻ = trans AA.identᴿ (trans b⁺≃b⁻ (sym AA.identᴸ))
         in ∨-introᴿ (≃ᶻ-intro b⁺+0≃0+b⁻)
