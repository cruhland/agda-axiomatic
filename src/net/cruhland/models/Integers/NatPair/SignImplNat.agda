import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; neg≄0; Positive; Positivity; pos≄0)
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; contra)

module net.cruhland.models.Integers.NatPair.SignImplNat
  (PA : PeanoArithmetic) where

private open module ℕ = PeanoArithmetic PA using (ℕ)
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (Z+)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.BaseImpl PA as ℤB
  using (_—_; ℤ; ≃₀-intro)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (Z-)
import net.cruhland.models.Integers.NatPair.NegationImpl PA as ℤ-

import net.cruhland.axioms.Integers.SignDecl PA as SignDecl
open SignDecl.SignPredefs ZB Z+ Z- using (_≃_[posℕ]; ≃posℕ-intro)

nonzero-from-≃id[posℕ] : ∀ {a} → a ≃ id [posℕ] → a ≄ 0
nonzero-from-≃id[posℕ] (≃posℕ-intro pos[n] a≃n) a≃0 =
  let n≃0 = AA.inject (Eq.trans (Eq.sym a≃n) a≃0)
      n≄0 = pos≄0 pos[n]
   in contra n≃0 n≄0

instance
  pos-substitutive : AA.Substitutive₁ (_≃ id [posℕ]) _≃_ _⟨→⟩_
  pos-substitutive = AA.substitutive₁ pos-subst
    where
      pos-subst : ∀ {a b} → a ≃ b → a ≃ id [posℕ] → b ≃ id [posℕ]
      pos-subst a≃b (≃posℕ-intro pos[n] a≃n) =
        ≃posℕ-intro pos[n] (Eq.trans (Eq.sym a≃b) a≃n)

  positivity : Positivity {A = ℤ} 0
  positivity =
    record { Positive = _≃ id [posℕ] ; pos≄0 = nonzero-from-≃id[posℕ] }

nonzero-from-≃neg[posℕ] : ∀ {a} → a ≃ -_ [posℕ] → a ≄ 0
nonzero-from-≃neg[posℕ] {a} (≃posℕ-intro {n} pos[n] a≃-n) a≃0 =
  let n≃0 =
        begin
          (n as ℤ)
        ≃˘⟨ ℤ-.neg-involutive ⟩
          - (- (n as ℤ))
        ≃˘⟨ AA.subst₁ a≃-n ⟩
          - a
        ≃⟨ AA.subst₁ a≃0 ⟩
          - 0
        ≃⟨ ℤ-.neg-zero ⟩
          0
        ∎
      n≄0 = pos≄0 pos[n]
   in contra (AA.inject n≃0) n≄0

instance
  neg-substitutive : AA.Substitutive₁ (_≃ -_ [posℕ]) _≃_ _⟨→⟩_
  neg-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : ∀ {a b} → a ≃ b → a ≃ -_ [posℕ] → b ≃ -_ [posℕ]
      neg-subst a≃b (≃posℕ-intro pos[n] a≃n) =
        ≃posℕ-intro pos[n] (Eq.trans (Eq.sym a≃b) a≃n)

  negativity : Negativity {A = ℤ} 0
  negativity =
    record { Negative = _≃ -_ [posℕ] ; neg≄0 = nonzero-from-≃neg[posℕ] }

posℕ-from-posℤ : {a : ℤ} → Positive a → a ≃ id [posℕ]
posℕ-from-posℤ = id

posℕ-from-negℤ : {a : ℤ} → Negative a → a ≃ -_ [posℕ]
posℕ-from-negℤ = id

posℤ-from-posℕ : {a : ℤ} → a ≃ id [posℕ] → Positive a
posℤ-from-posℕ = id

negℤ-from-posℕ : {a : ℤ} → a ≃ -_ [posℕ] → Negative a
negℤ-from-posℕ = id

from-ℕ-preserves-pos : {n : ℕ} → Positive n → Positive (n as ℤ)
from-ℕ-preserves-pos pos[n] = ≃posℕ-intro pos[n] Eq.refl

neg-Positive : {a : ℤ} → Positive a → Negative (- a)
neg-Positive (≃posℕ-intro pos[n] a≃n) =
  let -a≃-n = AA.subst₁ a≃n
   in ≃posℕ-intro pos[n] -a≃-n

neg-Negative : {a : ℤ} → Negative a → Positive (- a)
neg-Negative {a} (≃posℕ-intro {n} pos[n] a≃-n) =
  let -a≃n =
        begin
          - a
        ≃⟨ AA.subst₁ a≃-n ⟩
          - (- (n as ℤ))
        ≃⟨ ℤ-.neg-involutive ⟩
          (n as ℤ)
        ∎
   in ≃posℕ-intro pos[n] -a≃n

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
          x⁺+d≃0+x⁻ =
            begin
              x⁺ + d
            ≃⟨ x⁺+d≃x⁻ ⟩
              x⁻
            ≃˘⟨ AA.ident ⟩
              0 + x⁻
            ∎
       in AA.1st (≃posℕ-intro pos[d] (≃₀-intro x⁺+d≃0+x⁻))
    1of3 | AA.2nd x⁺≃x⁻ = AA.2nd (ℤB.zero-from-balanced x⁺≃x⁻)
    1of3 | AA.3rd x⁺>x⁻ =
      let d = ℕ.<-diff x⁺>x⁻
          pos[d] = ℕ.<-diff-pos x⁺>x⁻
          x⁻+d≃x⁺ = ℕ.<-elim-diff x⁺>x⁻
          x⁺+0≃d+x⁻ =
            begin
              x⁺ + 0
            ≃⟨ AA.ident ⟩
              x⁺
            ≃˘⟨ x⁻+d≃x⁺ ⟩
              x⁻ + d
            ≃⟨ AA.comm ⟩
              d + x⁻
            ∎
       in AA.3rd (≃posℕ-intro pos[d] (≃₀-intro x⁺+0≃d+x⁻))

    ¬2of3 : ¬ AA.TwoOfThree (Negative x) (x ≃ 0) (Positive x)
    ¬2of3 (AA.2∧3 x≃0 pos[x]) = contra x≃0 (pos≄0 pos[x])
    ¬2of3 (AA.1∧2 neg[x] x≃0) = contra x≃0 (neg≄0 neg[x])
    ¬2of3
      (AA.1∧3
        (≃posℕ-intro {n} pos[n] (≃₀-intro x⁺+n≃0+x⁻))
        (≃posℕ-intro {m} pos[m] (≃₀-intro x⁺+0≃m+x⁻))) =
      let x⁺+n≃x⁻ =
            begin
              x⁺ + n
            ≃⟨ x⁺+n≃0+x⁻ ⟩
              0 + x⁻
            ≃⟨ AA.ident ⟩
              x⁻
            ∎
          x⁻+m≃x⁺ =
            begin
              x⁻ + m
            ≃⟨ AA.comm ⟩
              m + x⁻
            ≃˘⟨ x⁺+0≃m+x⁻ ⟩
              x⁺ + 0
            ≃⟨ AA.ident ⟩
              x⁺
            ∎
          x⁺<x⁻ = ℕ.<-intro-diff pos[n] x⁺+n≃x⁻
          x⁻<x⁺ = ℕ.<-intro-diff pos[m] x⁻+m≃x⁺
          x⁺<>x⁻ = AA.1∧3 x⁺<x⁻ x⁻<x⁺
          ¬x⁺<>x⁻ = AA.ExactlyOneOfThree.at-most-one x⁺<≃>x⁻
       in contra x⁺<>x⁻ ¬x⁺<>x⁻

-- Include everything from the partial impl
open import net.cruhland.axioms.Integers.SignPartialImpl PA ZB Z+ Z-
  using (SignProperties)
open SignProperties (record { from-ℕ-preserves-pos = from-ℕ-preserves-pos })
  public hiding (from-ℕ-preserves-pos; positivity)
