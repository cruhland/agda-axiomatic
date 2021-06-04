import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; neg≄0; Positive; Positivity; pos≄0)
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; contra)

module net.cruhland.models.Integers.NatPair.Sign.BaseImplNat
  (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (_—_; ℤ; ≃₀-intro)
import net.cruhland.models.Integers.NatPair.NegationImpl PA as ℤ-

record _≃Posℕ (a : ℤ) : Set where
  constructor intro-Posℕ
  field
    {n} : ℕ
    pos[n] : Positive n
    n≃a : (n as ℤ) ≃ a

Posℕ≄0 : ∀ {a} → a ≃Posℕ → a ≄ 0
Posℕ≄0 (intro-Posℕ pos[n] n≃a) a≃0 =
  let n≃0 = AA.inject (Eq.trans n≃a a≃0)
      n≄0 = pos≄0 pos[n]
   in contra n≃0 n≄0

instance
  pos-substitutive : AA.Substitutive₁ _≃Posℕ _≃_ _⟨→⟩_
  pos-substitutive = AA.substitutive₁ pos-subst
    where
      pos-subst : ∀ {a b} → a ≃ b → a ≃Posℕ → b ≃Posℕ
      pos-subst a≃b (intro-Posℕ pos[n] n≃a) =
        intro-Posℕ pos[n] (Eq.trans n≃a a≃b)

  positivity : Positivity {A = ℤ} 0
  positivity = record { Positive = _≃Posℕ ; pos≄0 = Posℕ≄0 }

record _≃-Posℕ (a : ℤ) : Set where
  constructor intro-neg-Posℕ
  field
    {n} : ℕ
    pos[n] : Positive n
    -n≃a : - (n as ℤ) ≃ a

neg-Posℕ≄0 : ∀ {a} → a ≃-Posℕ → a ≄ 0
neg-Posℕ≄0 {a} (intro-neg-Posℕ {n} pos[n] -n≃a) a≃0 =
  let n≃0 =
        begin
          (n as ℤ)
        ≃˘⟨ ℤ-.neg-involutive ⟩
          - (- (n as ℤ))
        ≃⟨ AA.subst₁ -n≃a ⟩
          - a
        ≃⟨ AA.subst₁ a≃0 ⟩
          - 0
        ≃⟨ ℤ-.neg-zero ⟩
          0
        ∎
      n≄0 = pos≄0 pos[n]
   in contra (AA.inject n≃0) n≄0

instance
  neg-substitutive : AA.Substitutive₁ _≃-Posℕ _≃_ _⟨→⟩_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : ∀ {a b} → a ≃ b → a ≃-Posℕ → b ≃-Posℕ
      neg-subst a≃b (intro-neg-Posℕ pos[n] n≃a) =
        intro-neg-Posℕ pos[n] (Eq.trans n≃a a≃b)

  negativity : Negativity {A = ℤ} 0
  negativity = record { Negative = _≃-Posℕ ; neg≄0 = neg-Posℕ≄0 }

from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)
from-ℕ-preserves-pos pos[n] = intro-Posℕ pos[n] Eq.refl

neg-Positive : {a : ℤ} → Positive a → Negative (- a)
neg-Positive (intro-Posℕ pos[n] n≃a) =
  let -n≃-a = AA.subst₁ n≃a
   in intro-neg-Posℕ pos[n] -n≃-a

neg-Negative : {a : ℤ} → Negative a → Positive (- a)
neg-Negative {a} (intro-neg-Posℕ {n} pos[n] -n≃a) =
  let n≃-a =
        begin
          (n as ℤ)
        ≃˘⟨ ℤ-.neg-involutive ⟩
          - (- (n as ℤ))
        ≃⟨ AA.subst₁ -n≃a ⟩
          - a
        ∎
   in intro-Posℕ pos[n] n≃-a

trichotomy : (a : ℤ) → AA.ExactlyOneOfThree (Negative a) (a ≃ 0) (Positive a)
trichotomy x@(x⁺ — x⁻) = AA.exactlyOneOfThree 1of3 ¬2of3
  where
    x⁺<≃>x⁻ = ℕ.order-trichotomy x⁺ x⁻

    1of3 : AA.OneOfThree (Negative x) (x ≃ 0) (Positive x)
    1of3 with AA.ExactlyOneOfThree.at-least-one x⁺<≃>x⁻
    1of3 | AA.1st x⁺<x⁻ =
      let d = ℕ.<-diff x⁺<x⁻
          pos[d] = ℕ.<-diff-pos x⁺<x⁻
          x⁺+d≃x⁻ = ℕ.<-elim-diff x⁺<x⁻
          0+x⁻≃x⁺+d =
            begin
              0 + x⁻
            ≃⟨ AA.ident ⟩
              x⁻
            ≃˘⟨ x⁺+d≃x⁻ ⟩
              x⁺ + d
            ∎
       in AA.1st (intro-neg-Posℕ pos[d] (≃₀-intro 0+x⁻≃x⁺+d))
    1of3 | AA.2nd x⁺≃x⁻ = AA.2nd (ℤB.zero-from-balanced x⁺≃x⁻)
    1of3 | AA.3rd x⁺>x⁻ =
      let d = ℕ.<-diff x⁺>x⁻
          pos[d] = ℕ.<-diff-pos x⁺>x⁻
          x⁻+d≃x⁺ = ℕ.<-elim-diff x⁺>x⁻
          d+x⁻≃x⁺+0 =
            begin
              d + x⁻
            ≃⟨ AA.comm ⟩
              x⁻ + d
            ≃⟨ x⁻+d≃x⁺ ⟩
              x⁺
            ≃˘⟨ AA.ident ⟩
              x⁺ + 0
            ∎
       in AA.3rd (intro-Posℕ pos[d] (≃₀-intro d+x⁻≃x⁺+0))

    ¬2of3 : ¬ AA.TwoOfThree (Negative x) (x ≃ 0) (Positive x)
    ¬2of3 (AA.2∧3 x≃0 pos[x]) = contra x≃0 (pos≄0 pos[x])
    ¬2of3 (AA.1∧2 neg[x] x≃0) = contra x≃0 (neg≄0 neg[x])
    ¬2of3
      (AA.1∧3
        (intro-neg-Posℕ {n} pos[n] (≃₀-intro 0+x⁻≃x⁺+n))
        (intro-Posℕ {m} pos[m] (≃₀-intro m+x⁻≃x⁺+0))) =
      let x⁺+n≃x⁻ =
            begin
              x⁺ + n
            ≃˘⟨ 0+x⁻≃x⁺+n ⟩
              0 + x⁻
            ≃⟨ AA.ident ⟩
              x⁻
            ∎
          x⁻+m≃x⁺ =
            begin
              x⁻ + m
            ≃⟨ AA.comm ⟩
              m + x⁻
            ≃⟨ m+x⁻≃x⁺+0 ⟩
              x⁺ + 0
            ≃⟨ AA.ident ⟩
              x⁺
            ∎
          x⁺<x⁻ = ℕ.<-intro-diff pos[n] x⁺+n≃x⁻
          x⁻<x⁺ = ℕ.<-intro-diff pos[m] x⁻+m≃x⁺
          x⁺<>x⁻ = AA.1∧3 x⁺<x⁻ x⁻<x⁺
          ¬x⁺<>x⁻ = AA.ExactlyOneOfThree.at-most-one x⁺<≃>x⁻
       in contra x⁺<>x⁻ ¬x⁺<>x⁻
