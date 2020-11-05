-- Needed for positive integer literals
import Agda.Builtin.FromNat as FromNat
open import Agda.Builtin.FromNeg using (Negative)
open import Function using (_∘_)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq using
  (_≃_; refl; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Logic using (⊤; ¬_)

module net.cruhland.models.Integers.Negation (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (ℕ)
import net.cruhland.models.Integers.Addition PA as Addition
open Addition using (fromNat; fromℕ; +-identityᴿ)
open import net.cruhland.models.Integers.Base PA using (_—_; ℤ)
import net.cruhland.models.Integers.Equality PA as Equality
open Equality using (≃ᶻ-elim; ≃ᶻ-intro)

instance
  neg-dash : Op.Dashᴸ ℤ
  neg-dash = record { -_ = λ { (a — b) → b — a } }

  negative : Negative ℤ
  negative = record { Constraint = λ _ → ⊤ ; fromNeg = λ n → - fromNat n }

  neg-substitutive : AA.Substitutive₁ (λ x → - x)
  neg-substitutive = record { subst = neg-subst }
    where
      neg-subst : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
      neg-subst {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} a₁≃a₂ = ≃ᶻ-intro eq′
        where
          a₁⁺+a₂⁻≃a₂⁺+a₁⁻ = ≃ᶻ-elim a₁≃a₂
          eq′ =
            begin
              a₁⁻ + a₂⁺
            ≃⟨ AA.comm ⟩
              a₂⁺ + a₁⁻
            ≃˘⟨ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
              a₁⁺ + a₂⁻
            ≃⟨ AA.comm ⟩
              a₂⁻ + a₁⁺
            ∎

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive = ≃ᶻ-intro refl

+-inverseᴸ : {x : ℤ} → - x + x ≃ 0
+-inverseᴸ {x⁺ — x⁻} = ≃ᶻ-intro [x⁻+x⁺]+0≃0+[x⁺+x⁻]
  where
    [x⁻+x⁺]+0≃0+[x⁺+x⁻] =
      begin
        (x⁻ + x⁺) + 0
      ≃⟨ AA.comm ⟩
        0 + (x⁻ + x⁺)
      ≃⟨ AA.substᴿ AA.comm ⟩
        0 + (x⁺ + x⁻)
      ∎

+-inverseᴿ : {x : ℤ} → x + - x ≃ 0
+-inverseᴿ {x} =
  begin
    x + - x
  ≃⟨ AA.comm ⟩
    - x + x
  ≃⟨ +-inverseᴸ ⟩
    0
  ∎

instance
  sub-dash : Op.Dash₂ ℤ
  sub-dash = Op.subtraction

sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
sub-substᴸ = AA.substᴸ

sub-substᴿ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a - b₁ ≃ a - b₂
sub-substᴿ = AA.substᴿ ∘ AA.subst

≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ +-identityᴿ ⟩
    a + 0
  ≃˘⟨ AA.substᴿ +-inverseᴿ ⟩
    a + (b - b)
  ≃⟨ AA.substᴿ AA.comm ⟩
    a + (- b + b)
  ≃˘⟨ AA.assoc ⟩
    a - b + b
  ≃⟨ AA.substᴸ a-b≃c ⟩
    c + b
  ≃⟨ AA.comm ⟩
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

trichotomy : ∀ x → Trichotomy x
trichotomy (x⁺ — x⁻) = record { at-least = one≤ ; at-most = one≮ }
  where
    one≤ : AtLeastOne (x⁺ — x⁻)
    one≤ with ℕ.trichotomy {x⁺} {x⁻}
    one≤ | ℕ.tri-< x⁺<x⁻ =
        let record { d = n ; d≄z = pos-n ; n+d≃m = x⁺+n≃x⁻ } = ℕ.<→<⁺ x⁺<x⁻
            x⁺+n≃0+x⁻ =
              begin
                x⁺ + n
              ≃⟨ x⁺+n≃x⁻ ⟩
                x⁻
              ≃˘⟨ AA.identᴸ ⟩
                0 + x⁻
              ∎
         in neg (record { n = n ; pos = pos-n ; x≃-n = ≃ᶻ-intro x⁺+n≃0+x⁻ })
    one≤ | ℕ.tri-≃ x⁺≃x⁻ =
      nil (≃ᶻ-intro (trans AA.identᴿ (trans x⁺≃x⁻ (sym AA.identᴸ))))
    one≤ | ℕ.tri-> x⁺>x⁻ =
      let record { d = n ; d≄z = pos-n ; n+d≃m = x⁻+n≃x⁺ } = ℕ.<→<⁺ x⁺>x⁻
          x⁺—x⁻≃n =
            begin
              x⁺ + 0
            ≃⟨ AA.identᴿ ⟩
              x⁺
            ≃˘⟨ x⁻+n≃x⁺ ⟩
              x⁻ + n
            ≃⟨ AA.comm ⟩
              n + x⁻
            ∎
       in pos (record { n = n ; pos = pos-n ; x≃n = ≃ᶻ-intro x⁺—x⁻≃n })

    one≮ : ¬ MoreThanOne (x⁺ — x⁻)
    one≮ (nil∧pos
            (≃ᶻ-intro x⁺+0≃0+x⁻)
            record { n = n ; pos = n≄0 ; x≃n = ≃ᶻ-intro x⁺+0≃n+x⁻ }) =
      let x⁻+n≃x⁻+0 =
            begin
              x⁻ + n
            ≃⟨ AA.comm ⟩
              n + x⁻
            ≃˘⟨ x⁺+0≃n+x⁻ ⟩
              x⁺ + 0
            ≃⟨ x⁺+0≃0+x⁻ ⟩
              0 + x⁻
            ≃⟨ AA.comm ⟩
              x⁻ + 0
            ∎
       in n≄0 (AA.cancelᴸ x⁻+n≃x⁻+0)
    one≮ (nil∧neg
            (≃ᶻ-intro x⁺+0≃x⁻)
            record { n = n ; pos = n≄0 ; x≃-n = ≃ᶻ-intro x⁺+n≃x⁻ }) =
      n≄0 (AA.cancelᴸ (trans x⁺+n≃x⁻ (sym x⁺+0≃x⁻)))
    one≮ (pos∧neg
            record { n = n₁ ; pos = n₁≄0 ; x≃n = ≃ᶻ-intro x⁺+0≃n₁+x⁻ }
            record { n = n₂ ; pos = n₂≄0 ; x≃-n = ≃ᶻ-intro x⁺+n₂≃0+x⁻ }) =
      let x⁺+[n₂+n₁]≃x⁺+0 =
            begin
              x⁺ + (n₂ + n₁)
            ≃˘⟨ AA.assoc ⟩
              (x⁺ + n₂) + n₁
            ≃⟨ AA.substᴸ x⁺+n₂≃0+x⁻ ⟩
              (0 + x⁻) + n₁
            ≃⟨ AA.substᴸ AA.identᴸ ⟩
              x⁻ + n₁
            ≃⟨ AA.comm ⟩
              n₁ + x⁻
            ≃˘⟨ x⁺+0≃n₁+x⁻ ⟩
              x⁺ + 0
            ∎
       in ℕ.+-positive n₂≄0 (AA.cancelᴸ x⁺+[n₂+n₁]≃x⁺+0)
