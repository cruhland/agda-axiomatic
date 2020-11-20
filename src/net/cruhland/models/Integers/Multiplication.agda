open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_; _*_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_∨_; ∨-introᴸ; ∨-introᴿ)

module net.cruhland.models.Integers.Multiplication (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
import net.cruhland.models.Integers.Addition PA as ℤ+
open import net.cruhland.models.Integers.Base PA as ℤ using (_—_; ℤ)
open import net.cruhland.models.Integers.Equality PA as ℤ≃ using (≃ᶻ-intro)
import net.cruhland.models.Integers.Literals PA as ℤLit
open import net.cruhland.models.Integers.Negation PA as ℤ-

instance
  star : Op.Star ℤ
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
      *-substᴸ {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} {b⁺ — b⁻} (≃ᶻ-intro a₁⁺a₂⁻≃a₂⁺a₁⁻) =
          ≃ᶻ-intro [a₁⁺b⁺+a₁⁻b⁻]+[a₂⁺b⁻+a₂⁻b⁺]≃[a₂⁺b⁺+a₂⁻b⁻]+[a₁⁺b⁻+a₁⁻b⁺]
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

          [a₁⁺b⁺+a₁⁻b⁻]+[a₂⁺b⁻+a₂⁻b⁺]≃[a₂⁺b⁺+a₂⁻b⁻]+[a₁⁺b⁻+a₁⁻b⁺] =
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

  *-compatible-ℕ : AA.Compatible₂ {A = ℕ} (_as ℤ) _*_ _*_
  *-compatible-ℕ = record { compat₂ = *-compat-ℕ }
    where
      *-compat-ℕ : {n m : ℕ} → (n * m as ℤ) ≃ (n as ℤ) * (m as ℤ)
      *-compat-ℕ {n} {m} = ≃ᶻ-intro nm+n0+0m≃nm+00+0
        where
          nm+n0+0m≃nm+00+0 =
            begin
              n * m + (n * 0 + 0 * m)
            ≃⟨ AA.substᴿ (AA.substᴸ AA.absorbᴿ) ⟩
              n * m + (0 + 0 * m)
            ≃˘⟨ AA.substᴿ (AA.substᴸ AA.absorbᴸ) ⟩
              n * m + (0 * 0 + 0 * m)
            ≃⟨ AA.substᴿ (AA.substᴿ AA.absorbᴸ) ⟩
              n * m + (0 * 0 + 0)
            ≃˘⟨ AA.assoc ⟩
              n * m + 0 * 0 + 0
            ∎

  *-identityᴸ : AA.Identityᴸ _*_ 1
  *-identityᴸ = record { identᴸ = *-identᴸ }
    where
      *-identᴸ : {x : ℤ} → 1 * x ≃ x
      *-identᴸ {x⁺ — x⁻} = ≃ᶻ-intro [1x⁺+0x⁻]+x⁻≃x⁺+[1x⁻+0x⁺]
        where
          [1x⁺+0x⁻]+x⁻≃x⁺+[1x⁻+0x⁺] =
            begin
              (1 * x⁺ + 0 * x⁻) + x⁻
            ≃⟨ AA.substᴸ (AA.substᴸ AA.identᴸ) ⟩
              (x⁺ + 0 * x⁻) + x⁻
            ≃⟨ AA.substᴸ (AA.substᴿ AA.absorbᴸ) ⟩
              (x⁺ + 0) + x⁻
            ≃⟨ AA.substᴸ AA.identᴿ ⟩
              x⁺ + x⁻
            ≃˘⟨ AA.substᴿ AA.identᴿ ⟩
              x⁺ + (x⁻ + 0)
            ≃˘⟨ AA.substᴿ (AA.substᴿ AA.absorbᴸ) ⟩
              x⁺ + (x⁻ + 0 * x⁺)
            ≃˘⟨ AA.substᴿ (AA.substᴸ AA.identᴸ) ⟩
              x⁺ + (1 * x⁻ + 0 * x⁺)
            ∎

  *-identityᴿ : AA.Identityᴿ {A = ℤ} _*_ 1
  *-identityᴿ = AA.identityᴿ

  *-distributive-+ᴸ : AA.Distributiveᴸ _*_ _+_
  *-distributive-+ᴸ = record { distribᴸ = *-distrib-+ᴸ }
    where
      *-distrib-+ᴸ : {x y z : ℤ} → x * (y + z) ≃ x * y + x * z
      *-distrib-+ᴸ {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} =
          ≃ᶻ-intro
            (AA.[a≃b][c≃d] (refactor {x⁺} {x⁻})
            (sym (refactor {x⁺} {x⁻})))
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

  *-distributive-+ᴿ : AA.Distributiveᴿ {A = ℤ} _*_ _+_
  *-distributive-+ᴿ = AA.distributiveᴿ

  *-associative : AA.Associative _*_
  *-associative = record { assoc = *-assoc }
    where
      *-assoc : {x y z : ℤ} → (x * y) * z ≃ x * (y * z)
      *-assoc {x⁺ — x⁻} {y⁺ — y⁻} {z⁺ — z⁻} = ≃ᶻ-intro eq′
        where
          assoc-four :
            ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃} →
              ((a₁ * a₂) * a₃ + (b₁ * b₂) * b₃) +
              ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃) ≃
              (a₁ * (a₂ * a₃) + b₁ * (b₂ * b₃)) +
              (c₁ * (c₂ * c₃) + d₁ * (d₂ * d₃))
          assoc-four
              {a₁} {a₂} {a₃} {b₁} {b₂} {b₃} {c₁} {c₂} {c₃} {d₁} {d₂} {d₃} =
            begin
              ((a₁ * a₂) * a₃ + (b₁ * b₂) * b₃) +
              ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃)
            ≃⟨ AA.substᴸ (AA.substᴸ AA.assoc) ⟩
              (a₁ * (a₂ * a₃) + (b₁ * b₂) * b₃) +
              ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃)
            ≃⟨ AA.substᴸ (AA.substᴿ AA.assoc) ⟩
              (a₁ * (a₂ * a₃) + b₁ * (b₂ * b₃)) +
              ((c₁ * c₂) * c₃ + (d₁ * d₂) * d₃)
            ≃⟨ AA.substᴿ (AA.substᴸ AA.assoc) ⟩
              (a₁ * (a₂ * a₃) + b₁ * (b₂ * b₃)) +
              (c₁ * (c₂ * c₃) + (d₁ * d₂) * d₃)
            ≃⟨ AA.substᴿ (AA.substᴿ AA.assoc) ⟩
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

  *-commutative-negᴸ : AA.Commutativeᴸ -_ _*_
  *-commutative-negᴸ = record { commᴸ = *-negᴸ }
    where
      *-negᴸ : {a b : ℤ} → - a * b ≃ - (a * b)
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

  *-commutative-negᴿ : AA.Commutativeᴿ -_ _*_
  *-commutative-negᴿ = AA.commutativeᴿ

neg-mult : {a : ℤ} → - a ≃ -1 * a
neg-mult {a⁺ — a⁻} = AA.[a≃b][c≃d] x≃0y+1x x≃0y+1x
  where
    x≃0y+1x : {x y : ℕ} → x ≃ 0 * y + 1 * x
    x≃0y+1x {x} {y} =
      begin
        x
      ≃˘⟨ AA.identᴸ ⟩
        0 + x
      ≃˘⟨ AA.substᴸ AA.absorbᴸ ⟩
        0 * y + x
      ≃˘⟨ AA.substᴿ AA.identᴸ ⟩
        0 * y + 1 * x
      ∎

*-distrib-subᴸ : {a b c : ℤ} → c * (a - b) ≃ c * a - c * b
*-distrib-subᴸ {a} {b} {c} =
  begin
    c * (a - b)
  ≃⟨⟩
    c * (a + - b)
  ≃⟨ AA.distribᴸ ⟩
    c * a + c * - b
  ≃⟨ AA.substᴿ {_⊙_ = _+_} AA.commᴿ ⟩
    c * a + - (c * b)
  ≃⟨⟩
    c * a - c * b
  ∎

*-distrib-subᴿ : {a b c : ℤ} → (a - b) * c ≃ a * c - b * c
*-distrib-subᴿ {a} {b} {c} =
  begin
    (a - b) * c
  ≃⟨⟩
    (a + - b) * c
  ≃⟨ AA.distribᴿ ⟩
    a * c + (- b) * c
  ≃⟨ AA.substᴿ AA.commᴸ ⟩
    a * c + - (b * c)
  ≃⟨⟩
    a * c - b * c
  ∎

instance
  *-absorptiveᴸ : AA.Absorptiveᴸ _*_ 0
  *-absorptiveᴸ = record { absorbᴸ = *-zeroᴸ }
    where
      *-zeroᴸ : {x : ℤ} → 0 * x ≃ 0
      *-zeroᴸ {x} =
        begin
          0 * x
        ≃˘⟨ AA.substᴸ AA.invᴿ ⟩
          (1 - 1) * x
        ≃⟨ *-distrib-subᴿ ⟩
          1 * x - 1 * x
        ≃⟨ AA.invᴿ ⟩
          0
        ∎

  *-absorptiveᴿ : AA.Absorptiveᴿ {A = ℤ} _*_ 0
  *-absorptiveᴿ = AA.absorptiveᴿ

neg-sub-swap : ∀ {a b} → - (a - b) ≃ b - a
neg-sub-swap {a} {b} =
  begin
    - (a - b)
  ≃⟨ neg-mult ⟩
    -1 * (a - b)
  ≃⟨ *-distrib-subᴸ {a} {b} { -1} ⟩
    -1 * a - -1 * b
  ≃˘⟨ AA.substᴸ neg-mult ⟩
    - a - -1 * b
  ≃˘⟨ AA.substᴿ (AA.subst neg-mult) ⟩
    - a - (- b)
  ≃⟨ AA.substᴿ neg-involutive ⟩
    - a + b
  ≃˘⟨ AA.comm ⟩
    b - a
  ∎

sub-sign-swap : ∀ {a b} → Negative (a - b) → Positive (b - a)
sub-sign-swap {a} {b} record { n = n ; pos = n≄0 ; x≃-n = a-b≃-n } =
    record { n = n ; pos = n≄0 ; x≃n = b-a≃n }
  where
    b-a≃n =
      begin
        b - a
      ≃˘⟨ neg-sub-swap {a} ⟩
        - (a - b)
      ≃⟨ AA.subst a-b≃-n ⟩
        - - (n as ℤ)
      ≃⟨ neg-involutive {n as ℤ} ⟩
        (n as ℤ)
      ∎

instance
  zero-product : AA.ZeroProduct _*_ 0
  zero-product = record { zero-prod = *-either-zero }
    where
      b≃0 : ∀ {b} {n : ℕ} → n ≄ 0 → (n as ℤ) * b ≃ 0 → b ≃ 0
      b≃0 {b⁺ — b⁻} {n} n≄0 (≃ᶻ-intro nb⁺+0b⁻+0≃0+[nb⁻+0b⁺]) =
        let nb⁺≃nb⁻ =
              begin
                n * b⁺
              ≃˘⟨ AA.identᴿ ⟩
                n * b⁺ + 0
              ≃˘⟨ AA.substᴿ AA.absorbᴸ ⟩
                n * b⁺ + 0 * b⁻
              ≃˘⟨ AA.identᴿ ⟩
                n * b⁺ + 0 * b⁻ + 0
              ≃⟨ nb⁺+0b⁻+0≃0+[nb⁻+0b⁺] ⟩
                0 + (n * b⁻ + 0 * b⁺)
              ≃⟨ AA.identᴸ ⟩
                n * b⁻ + 0 * b⁺
              ≃⟨ AA.substᴿ AA.absorbᴸ ⟩
                n * b⁻ + 0
              ≃⟨ AA.identᴿ ⟩
                n * b⁻
              ∎
            b⁺≃b⁻ = AA.cancelᴸ {{c = fromWitnessFalse n≄0}} nb⁺≃nb⁻
            b⁺+0≃0+b⁻ = trans AA.identᴿ (trans b⁺≃b⁻ (sym AA.identᴸ))
         in ≃ᶻ-intro b⁺+0≃0+b⁻

      *-either-zero : ∀ {a b} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
      *-either-zero {a} {b} ab≃0 with
        AA.ExactlyOneOfThree.at-least-one (trichotomy a)
      *-either-zero {a} {b} ab≃0 | AA.2nd a≃0 =
        ∨-introᴸ a≃0
      *-either-zero {a} {b} ab≃0
          | AA.3rd record { n = n ; pos = n≄0 ; x≃n = a≃n—0 } =
        let nb≃0 =
              begin
                (n as ℤ) * b
              ≃⟨⟩
                n — 0 * b
              ≃˘⟨ AA.substᴸ a≃n—0 ⟩
                a * b
              ≃⟨ ab≃0 ⟩
                0
              ∎
         in ∨-introᴿ (b≃0 n≄0 nb≃0)
      *-either-zero {a} {b} ab≃0
          | AA.1st record { n = n ; pos = n≄0 ; x≃-n = a≃0—n } =
        let nb≃0 =
              begin
                (n as ℤ) * b
              ≃⟨⟩
                n — 0 * b
              ≃⟨⟩
                - 0 — n * b
              ≃˘⟨ AA.substᴸ (AA.subst a≃0—n) ⟩
                - a * b
              ≃⟨ AA.commᴸ ⟩
                - (a * b)
              ≃⟨ AA.subst ab≃0 ⟩
                - 0
              ≃⟨⟩
                0
              ∎
         in ∨-introᴿ (b≃0 n≄0 nb≃0)
