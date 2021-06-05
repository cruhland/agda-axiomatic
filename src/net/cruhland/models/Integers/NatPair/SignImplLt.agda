import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Ordering using (_<_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; neg≄0; Positive; Positivity; pos≄0)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; contra)

module net.cruhland.models.Integers.NatPair.SignImplLt
  (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (_—_; ℤ; ≃₀-intro)
import net.cruhland.models.Integers.NatPair.NegationImpl PA as ℤ-

Pos : ℤ → Set
Pos (a⁺ — a⁻) = a⁻ < a⁺

Neg : ℤ → Set
Neg (a⁺ — a⁻) = a⁺ < a⁻

Pos≄0 : ∀ {a} → Pos a → a ≄ 0
Pos≄0 {a⁺ — a⁻} a⁻<a⁺ a≃0 =
  let a⁻≃a⁺ = Eq.sym (ℤB.balanced-from-zero a≃0)
      a⁻≄a⁺ = ℕ.<-elim-≄ a⁻<a⁺
   in contra a⁻≃a⁺ a⁻≄a⁺

Neg≄0 : ∀ {a} → Neg a → a ≄ 0
Neg≄0 {a⁺ — a⁻} a⁺<a⁻ a≃0 =
  let a⁺≃a⁻ = ℤB.balanced-from-zero a≃0
      a⁺≄a⁻ = ℕ.<-elim-≄ a⁺<a⁻
   in contra a⁺≃a⁻ a⁺≄a⁻

instance
  Pos-substitutive : AA.Substitutive₁ Pos _≃_ _⟨→⟩_
  Pos-substitutive = AA.substitutive₁ Pos-subst
    where
      Pos-subst : ∀ {a b} → a ≃ b → Pos a → Pos b
      Pos-subst a@{a⁺ — a⁻} b@{b⁺ — b⁻} (≃₀-intro a⁺+b⁻≃b⁺+a⁻) a⁻<a⁺ =
        let d = ℕ.<-diff a⁻<a⁺
            pos[d] = ℕ.<-diff-pos a⁻<a⁺
            a⁻+d≃a⁺ = ℕ.<-elim-diff a⁻<a⁺
            [b⁻+d]+a⁻≃b⁺+a⁻ =
              begin
                (b⁻ + d) + a⁻
              ≃⟨ AA.assoc ⟩
                b⁻ + (d + a⁻)
              ≃⟨ AA.subst₂ AA.comm ⟩
                b⁻ + (a⁻ + d)
              ≃⟨ AA.subst₂ a⁻+d≃a⁺ ⟩
                b⁻ + a⁺
              ≃⟨ AA.comm ⟩
                a⁺ + b⁻
              ≃⟨ a⁺+b⁻≃b⁺+a⁻ ⟩
                b⁺ + a⁻
              ∎
            b⁻+d≃b⁺ = AA.cancel [b⁻+d]+a⁻≃b⁺+a⁻
         in ℕ.<-intro-diff pos[d] b⁻+d≃b⁺

  positivity : Positivity {A = ℤ} 0
  positivity = record { Positive = Pos ; pos≄0 = Pos≄0 }

  Neg-substitutive : AA.Substitutive₁ Neg _≃_ _⟨→⟩_
  Neg-substitutive = AA.substitutive₁ Neg-subst
    where
      Neg-subst : ∀ {a b} → a ≃ b → Neg a → Neg b
      Neg-subst a@{a⁺ — a⁻} b@{b⁺ — b⁻} (≃₀-intro a⁺+b⁻≃b⁺+a⁻) a⁺<a⁻ =
        let d = ℕ.<-diff a⁺<a⁻
            pos[d] = ℕ.<-diff-pos a⁺<a⁻
            a⁺+d≃a⁻ = ℕ.<-elim-diff a⁺<a⁻
            a⁺+b⁻≃a⁺+[b⁺+d] =
              begin
                a⁺ + b⁻
              ≃⟨ a⁺+b⁻≃b⁺+a⁻ ⟩
                b⁺ + a⁻
              ≃˘⟨ AA.subst₂ a⁺+d≃a⁻ ⟩
                b⁺ + (a⁺ + d)
              ≃˘⟨ AA.assoc ⟩
                (b⁺ + a⁺) + d
              ≃⟨ AA.subst₂ AA.comm ⟩
                (a⁺ + b⁺) + d
              ≃⟨ AA.assoc ⟩
                a⁺ + (b⁺ + d)
              ∎
            b⁺+d≃b⁻ = Eq.sym (AA.cancel a⁺+b⁻≃a⁺+[b⁺+d])
         in ℕ.<-intro-diff pos[d] b⁺+d≃b⁻

  negativity : Negativity {A = ℤ} 0
  negativity = record { Negative = Neg ; neg≄0 = Neg≄0 }

from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)
from-ℕ-preserves-pos = ℕ.<-from-pos

neg-Positive : {a : ℤ} → Positive a → Negative (- a)
neg-Positive {a⁺ — a⁻} a⁻<a⁺ = a⁻<a⁺

neg-Negative : {a : ℤ} → Negative a → Positive (- a)
neg-Negative {a⁺ — a⁻} a⁺<a⁻ = a⁺<a⁻

trichotomy : (a : ℤ) → AA.ExactlyOneOfThree (Negative a) (a ≃ 0) (Positive a)
trichotomy a@(a⁺ — a⁻) = AA.exactlyOneOfThree 1of3 ¬2of3
  where
    1of3 : AA.OneOfThree (Negative a) (a ≃ 0) (Positive a)
    1of3 with AA.ExactlyOneOfThree.at-least-one (ℕ.order-trichotomy a⁺ a⁻)
    1of3 | AA.1st a⁺<a⁻ = AA.1st a⁺<a⁻
    1of3 | AA.2nd a⁺≃a⁻ = AA.2nd (ℤB.zero-from-balanced a⁺≃a⁻)
    1of3 | AA.3rd a⁻<a⁺ = AA.3rd a⁻<a⁺

    ¬2of3 : ¬ AA.TwoOfThree (Negative a) (a ≃ 0) (Positive a)
    ¬2of3 (AA.1∧2 neg[a] a≃0) = contra a≃0 (neg≄0 neg[a])
    ¬2of3 (AA.1∧3 a⁺<a⁻ a⁻<a⁺) = ℕ.<-asymmetric a⁺<a⁻ a⁻<a⁺
    ¬2of3 (AA.2∧3 a≃0 pos[a]) = contra a≃0 (pos≄0 pos[a])

-- Include everything from the partial impl
open import net.cruhland.axioms.Integers.SignPartialImpl PA ZB
  using (SignProperties)
open SignProperties (record { from-ℕ-preserves-pos = from-ℕ-preserves-pos })
  public hiding (from-ℕ-preserves-pos; positivity)
