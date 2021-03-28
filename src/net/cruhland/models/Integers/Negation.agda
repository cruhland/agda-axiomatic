import Agda.Builtin.FromNeg as FromNeg
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; refl; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as Sign
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_)
open import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Logic using (⊤; ¬_; contra)

module net.cruhland.models.Integers.Negation (PA : PeanoArithmetic) where

private module ℕ = PeanoArithmetic PA
open ℕ using (_<⁺_; _>⁺_; ℕ)
import net.cruhland.models.Integers.Addition PA as ℤ+
open import net.cruhland.models.Integers.Base PA as ℤ using (_—_; ℤ)
open import net.cruhland.models.Integers.Equality PA as ℤ≃ using (≃ᶻ-intro)
import net.cruhland.models.Integers.Literals PA as ℤLit

instance
  neg-dash : Op.Dashᴸ ℤ
  neg-dash = record { -_ = λ { (a — b) → b — a } }

  negative : FromNeg.Negative ℤ
  negative =
    record { Constraint = λ _ → ⊤ ; fromNeg = λ n → - Literals.fromNat n }

  neg-substitutive : AA.Substitutive₁ -_ _≃_ _≃_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → - a₁ ≃ - a₂
      neg-subst {a₁⁺ — a₁⁻} {a₂⁺ — a₂⁻} (≃ᶻ-intro a₁⁺+a₂⁻≃a₂⁺+a₁⁻) =
          ≃ᶻ-intro a₁⁻+a₂⁺≃a₂⁻+a₁⁺
        where
          a₁⁻+a₂⁺≃a₂⁻+a₁⁺ =
            begin
              a₁⁻ + a₂⁺
            ≃⟨ AA.comm ⟩
              a₂⁺ + a₁⁻
            ≃˘⟨ a₁⁺+a₂⁻≃a₂⁺+a₁⁻ ⟩
              a₁⁺ + a₂⁻
            ≃⟨ AA.comm ⟩
              a₂⁻ + a₁⁺
            ∎

  +-inverseᴸ : AA.Inverse AA.handᴸ λ x → - x
  +-inverseᴸ = AA.inverse +-invᴸ
    where
      +-invᴸ : {x : ℤ} → - x + x ≃ 0
      +-invᴸ {x⁺ — x⁻} = ≃ᶻ-intro [x⁻+x⁺]+0≃0+[x⁺+x⁻]
        where
          [x⁻+x⁺]+0≃0+[x⁺+x⁻] =
            begin
              (x⁻ + x⁺) + 0
            ≃⟨ AA.comm ⟩
              0 + (x⁻ + x⁺)
            ≃⟨ AA.subst₂ AA.comm ⟩
              0 + (x⁺ + x⁻)
            ∎

  +-inverseᴿ : AA.Inverse AA.handᴿ λ x → - x
  +-inverseᴿ = AA.inverseᴿ-from-inverseᴸ

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive = ≃ᶻ-intro refl

instance
  sub-dash : Op.Dash₂ ℤ
  sub-dash = Op.subtraction

sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
sub-substᴸ = AA.subst₂

sub-substᴿ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a - b₁ ≃ a - b₂
sub-substᴿ = AA.subst₂ ∘ AA.subst₁

≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ AA.ident ⟩
    a + 0
  ≃˘⟨ AA.subst₂ AA.invᴿ ⟩
    a + (b - b)
  ≃⟨ AA.subst₂ AA.comm ⟩
    a + (- b + b)
  ≃˘⟨ AA.assoc ⟩
    a - b + b
  ≃⟨ AA.subst₂ a-b≃c ⟩
    c + b
  ≃⟨ AA.comm ⟩
    b + c
  ∎

record Positive (x : ℤ) : Set where
  field
    n : ℕ
    pos : Sign.Positive n
    x≃n : x ≃ (n as ℤ)

record Negative (x : ℤ) : Set where
  field
    n : ℕ
    pos : Sign.Positive n
    x≃-n : x ≃ - (n as ℤ)

1-Positive : Positive 1
1-Positive = record { n = 1 ; pos = ℕ.mkPositive ℕ.step≄zero ; x≃n = refl }

pos-nonzero : ∀ {a} → Positive a → a ≄ 0
pos-nonzero (record { n = n ; pos = pos-n ; x≃n = a≃n }) a≃0 =
  Sign.pos≄0 pos-n (AA.inject (trans (sym a≃n) a≃0))

instance
  Positive-substitutive : AA.Substitutive₁ Positive _≃_ _⟨→⟩_
  Positive-substitutive = AA.substitutive₁ Positive-subst
    where
      Positive-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → Positive a₁ → Positive a₂
      Positive-subst a₁≃a₂ (record { n = n ; pos = n≄0 ; x≃n = a₁≃n }) =
        record { n = n ; pos = n≄0 ; x≃n = trans (sym a₁≃a₂) a₁≃n }

neg-Positive : ∀ {a} → Positive a → Negative (- a)
neg-Positive record { n = n ; pos = n≄0 ; x≃n = a≃n } =
  record { n = n ; pos = n≄0 ; x≃-n = AA.subst₁ a≃n }

neg-Negative : ∀ {a} → Negative a → Positive (- a)
neg-Negative record { n = n ; pos = n≄0 ; x≃-n = a≃-n } =
  record { n = n ; pos = n≄0 ; x≃n = trans (AA.subst₁ a≃-n) neg-involutive }

trichotomy : ∀ x → AA.ExactlyOneOfThree (Negative x) (x ≃ 0) (Positive x)
trichotomy x@(x⁺ — x⁻) = record { at-least-one = one≤ ; at-most-one = one≮ }
  where
    one≤ : AA.OneOfThree (Negative x) (x ≃ 0) (Positive x)
    one≤ with AA.ExactlyOneOfThree.at-least-one (ℕ.order-trichotomy {x⁺} {x⁻})
    one≤ | AA.1st x⁺<x⁻ =
        let ℕ.<⁺-intro (ℕ.≤-intro n x⁺+n≃x⁻) n≄0 = x⁺<x⁻ as x⁺ <⁺ x⁻
            x⁺+n≃0+x⁻ =
              begin
                x⁺ + n
              ≃⟨ x⁺+n≃x⁻ ⟩
                x⁻
              ≃˘⟨ AA.ident ⟩
                0 + x⁻
              ∎
            pos-n = ℕ.mkPositive n≄0
         in AA.1st (record { n = n ; pos = pos-n ; x≃-n = ≃ᶻ-intro x⁺+n≃0+x⁻ })
    one≤ | AA.2nd x⁺≃x⁻ =
      AA.2nd (≃ᶻ-intro (trans AA.ident (trans x⁺≃x⁻ (sym AA.ident))))
    one≤ | AA.3rd x⁺>x⁻ =
      let ℕ.<⁺-intro (ℕ.≤-intro n x⁻+n≃x⁺) n≄0 = x⁺>x⁻ as x⁺ >⁺ x⁻
          x⁺—x⁻≃n =
            begin
              x⁺ + 0
            ≃⟨ AA.ident ⟩
              x⁺
            ≃˘⟨ x⁻+n≃x⁺ ⟩
              x⁻ + n
            ≃⟨ AA.comm ⟩
              n + x⁻
            ∎
          pos-n = ℕ.mkPositive n≄0
       in AA.3rd (record { n = n ; pos = pos-n ; x≃n = ≃ᶻ-intro x⁺—x⁻≃n })

    one≮ : ¬ AA.TwoOfThree (Negative x) (x ≃ 0) (Positive x)
    one≮ (AA.2∧3
            (≃ᶻ-intro x⁺+0≃0+x⁻)
            record { n = n ; pos = pos-n ; x≃n = ≃ᶻ-intro x⁺+0≃n+x⁻ }) =
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
       in contra (AA.cancel x⁻+n≃x⁻+0) (Sign.pos≄0 pos-n)
    one≮ (AA.1∧2
            record { n = n ; pos = pos-n ; x≃-n = ≃ᶻ-intro x⁺+n≃x⁻ }
            (≃ᶻ-intro x⁺+0≃x⁻)) =
      contra (AA.cancel (trans x⁺+n≃x⁻ (sym x⁺+0≃x⁻))) (Sign.pos≄0 pos-n)
    one≮ (AA.1∧3
            record { n = n₂ ; pos = pos-n₂ ; x≃-n = ≃ᶻ-intro x⁺+n₂≃0+x⁻ }
            record { n = n₁ ; pos = pos-n₁ ; x≃n = ≃ᶻ-intro x⁺+0≃n₁+x⁻ }) =
      let x⁺+[n₂+n₁]≃x⁺+0 =
            begin
              x⁺ + (n₂ + n₁)
            ≃˘⟨ AA.assoc ⟩
              (x⁺ + n₂) + n₁
            ≃⟨ AA.subst₂ x⁺+n₂≃0+x⁻ ⟩
              (0 + x⁻) + n₁
            ≃⟨ AA.subst₂ AA.ident ⟩
              x⁻ + n₁
            ≃⟨ AA.comm ⟩
              n₁ + x⁻
            ≃˘⟨ x⁺+0≃n₁+x⁻ ⟩
              x⁺ + 0
            ∎
          n₂+n₁≄0 = Sign.pos≄0 (ℕ.+-positive pos-n₂)
       in contra (AA.cancel x⁺+[n₂+n₁]≃x⁺+0) n₂+n₁≄0
