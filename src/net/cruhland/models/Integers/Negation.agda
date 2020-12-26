import Agda.Builtin.FromNeg as FromNeg
open import Function using (_∘_) renaming (Morphism to _⟨→⟩_)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; refl; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.models.Literals as Literals
open import net.cruhland.models.Logic using (⊤; ¬_)

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
  neg-substitutive = record { subst = neg-subst }
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

  +-inverseᴸ : AA.Inverseᴸ _+_ -_ 0
  +-inverseᴸ = record { invᴸ = +-invᴸ }
    where
      +-invᴸ : {x : ℤ} → - x + x ≃ 0
      +-invᴸ {x⁺ — x⁻} = ≃ᶻ-intro [x⁻+x⁺]+0≃0+[x⁺+x⁻]
        where
          [x⁻+x⁺]+0≃0+[x⁺+x⁻] =
            begin
              (x⁻ + x⁺) + 0
            ≃⟨ AA.comm ⟩
              0 + (x⁻ + x⁺)
            ≃⟨ AA.subst AA.comm ⟩
              0 + (x⁺ + x⁻)
            ∎

  +-inverseᴿ : AA.Inverseᴿ _+_ -_ 0
  +-inverseᴿ = AA.inverseᴿ

neg-involutive : {a : ℤ} → - (- a) ≃ a
neg-involutive = ≃ᶻ-intro refl

instance
  sub-dash : Op.Dash₂ ℤ
  sub-dash = Op.subtraction

sub-substᴸ : {a₁ a₂ b : ℤ} → a₁ ≃ a₂ → a₁ - b ≃ a₂ - b
sub-substᴸ = AA.subst

sub-substᴿ : {a b₁ b₂ : ℤ} → b₁ ≃ b₂ → a - b₁ ≃ a - b₂
sub-substᴿ = AA.subst ∘ AA.subst {f = -_}

≃ᴸ-subᴿ-toᴸ : {a b c : ℤ} → a - b ≃ c → a ≃ b + c
≃ᴸ-subᴿ-toᴸ {a} {b} {c} a-b≃c =
  begin
    a
  ≃˘⟨ AA.identᴿ ⟩
    a + 0
  ≃˘⟨ AA.subst AA.invᴿ ⟩
    a + (b - b)
  ≃⟨ AA.subst {f = a +_} AA.comm ⟩
    a + (- b + b)
  ≃˘⟨ AA.assoc ⟩
    a - b + b
  ≃⟨ AA.subst a-b≃c ⟩
    c + b
  ≃⟨ AA.comm ⟩
    b + c
  ∎

record Positive (x : ℤ) : Set where
  field
    n : ℕ
    pos : ℕ.Positive n
    x≃n : x ≃ (n as ℤ)

record Negative (x : ℤ) : Set where
  field
    n : ℕ
    pos : ℕ.Positive n
    x≃-n : x ≃ - (n as ℤ)

1-Positive : Positive 1
1-Positive = record { n = 1 ; pos = ℕ.step≄zero ; x≃n = refl }

pos-nonzero : ∀ {a} → Positive a → a ≄ 0
pos-nonzero (record { n = n ; pos = n≄0 ; x≃n = a≃n }) a≃0 =
  n≄0 (AA.inject (trans (sym a≃n) a≃0))

instance
  Positive-substitutive : AA.Substitutive₁ Positive _≃_ _⟨→⟩_
  Positive-substitutive = record { subst = Positive-subst }
    where
      Positive-subst : ∀ {a₁ a₂} → a₁ ≃ a₂ → Positive a₁ → Positive a₂
      Positive-subst a₁≃a₂ (record { n = n ; pos = n≄0 ; x≃n = a₁≃n }) =
        record { n = n ; pos = n≄0 ; x≃n = trans (sym a₁≃a₂) a₁≃n }

neg-Positive : ∀ {a} → Positive a → Negative (- a)
neg-Positive record { n = n ; pos = n≄0 ; x≃n = a≃n } =
  record { n = n ; pos = n≄0 ; x≃-n = AA.subst a≃n }

neg-Negative : ∀ {a} → Negative a → Positive (- a)
neg-Negative record { n = n ; pos = n≄0 ; x≃-n = a≃-n } =
  record { n = n ; pos = n≄0 ; x≃n = trans (AA.subst a≃-n) neg-involutive }

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
              ≃˘⟨ AA.identᴸ ⟩
                0 + x⁻
              ∎
         in AA.1st (record { n = n ; pos = n≄0 ; x≃-n = ≃ᶻ-intro x⁺+n≃0+x⁻ })
    one≤ | AA.2nd x⁺≃x⁻ =
      AA.2nd (≃ᶻ-intro (trans AA.identᴿ (trans x⁺≃x⁻ (sym AA.identᴸ))))
    one≤ | AA.3rd x⁺>x⁻ =
      let ℕ.<⁺-intro (ℕ.≤-intro n x⁻+n≃x⁺) n≄0 = x⁺>x⁻ as x⁺ >⁺ x⁻
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
       in AA.3rd (record { n = n ; pos = n≄0 ; x≃n = ≃ᶻ-intro x⁺—x⁻≃n })

    one≮ : ¬ AA.TwoOfThree (Negative x) (x ≃ 0) (Positive x)
    one≮ (AA.2∧3
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
    one≮ (AA.1∧2
            record { n = n ; pos = n≄0 ; x≃-n = ≃ᶻ-intro x⁺+n≃x⁻ }
            (≃ᶻ-intro x⁺+0≃x⁻)) =
      n≄0 (AA.cancelᴸ (trans x⁺+n≃x⁻ (sym x⁺+0≃x⁻)))
    one≮ (AA.1∧3
            record { n = n₂ ; pos = n₂≄0 ; x≃-n = ≃ᶻ-intro x⁺+n₂≃0+x⁻ }
            record { n = n₁ ; pos = n₁≄0 ; x≃n = ≃ᶻ-intro x⁺+0≃n₁+x⁻ }) =
      let x⁺+[n₂+n₁]≃x⁺+0 =
            begin
              x⁺ + (n₂ + n₁)
            ≃˘⟨ AA.assoc ⟩
              (x⁺ + n₂) + n₁
            ≃⟨ AA.subst x⁺+n₂≃0+x⁻ ⟩
              (0 + x⁻) + n₁
            ≃⟨ AA.subst AA.identᴸ ⟩
              x⁻ + n₁
            ≃⟨ AA.comm ⟩
              n₁ + x⁻
            ≃˘⟨ x⁺+0≃n₁+x⁻ ⟩
              x⁺ + 0
            ∎
       in ℕ.+-positive n₂≄0 (AA.cancelᴸ x⁺+[n₂+n₁]≃x⁺+0)
