import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Ordering as Ord using (_<_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (¬_; ¬-intro; _↯_)

module net.cruhland.models.Integers.NatPair.SignImplLt
  (PA : PeanoArithmetic) where

import net.cruhland.axioms.Integers.SignDecl PA as SignDecl
open import net.cruhland.models.Integers.NatPair.AdditionDefn PA using (ZA)
open import net.cruhland.models.Integers.NatPair.BaseDefn PA using (ZB)
open import net.cruhland.models.Integers.NatPair.NegationDefn PA using (ZN)

private module ℕ = PeanoArithmetic PA
private module ℤ where
  open import net.cruhland.axioms.Integers.LiteralImpl PA ZB public
  open import net.cruhland.models.Integers.NatPair.AdditionImpl PA public
  open import net.cruhland.models.Integers.NatPair.BaseImpl PA public
  open import net.cruhland.models.Integers.NatPair.NegationImpl PA public
  open SignDecl.SignPredefs ZB ZA ZN public

open ℕ using (ℕ)
open ℤ using (_—_; _≃_[posℕ]; ℤ)

Pos : ℤ → Set
Pos (a⁺ — a⁻) = a⁻ < a⁺

Neg : ℤ → Set
Neg (a⁺ — a⁻) = a⁺ < a⁻

Pos≄0 : ∀ {a} → Pos a → a ≄ 0
Pos≄0 {a⁺ — a⁻} a⁻<a⁺ = Eq.≄-intro λ a≃0 →
  let a⁻≃a⁺ = Eq.sym (ℤ.balanced-from-zero a≃0)
      a⁻≄a⁺ = ℕ.<-elim-≄ a⁻<a⁺
   in a⁻≃a⁺ ↯ a⁻≄a⁺

Neg≄0 : ∀ {a} → Neg a → a ≄ 0
Neg≄0 {a⁺ — a⁻} a⁺<a⁻ = Eq.≄-intro λ a≃0 →
  let a⁺≃a⁻ = ℤ.balanced-from-zero a≃0
      a⁺≄a⁻ = ℕ.<-elim-≄ a⁺<a⁻
   in a⁺≃a⁻ ↯ a⁺≄a⁻

instance
  Pos-substitutive : AA.Substitutive₁ Pos _≃_ _⟨→⟩_
  Pos-substitutive = AA.substitutive₁ Pos-subst
    where
      Pos-subst : ∀ {a b} → a ≃ b → Pos a → Pos b
      Pos-subst a@{a⁺ — a⁻} b@{b⁺ — b⁻} (ℤ.≃₀-intro a⁺+b⁻≃b⁺+a⁻) a⁻<a⁺ =
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

  positivity : S.Positivity ℤ
  positivity = record { Positive = Pos ; pos≄0 = Pos≄0 }

  Neg-substitutive : AA.Substitutive₁ Neg _≃_ _⟨→⟩_
  Neg-substitutive = AA.substitutive₁ Neg-subst
    where
      Neg-subst : ∀ {a b} → a ≃ b → Neg a → Neg b
      Neg-subst a@{a⁺ — a⁻} b@{b⁺ — b⁻} (ℤ.≃₀-intro a⁺+b⁻≃b⁺+a⁻) a⁺<a⁻ =
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

  negativity : S.Negativity ℤ
  negativity = record { Negative = Neg ; neg≄0 = Neg≄0 }

posℕ-from-posℤ : {a : ℤ} → S.Positive a → a ≃ id [posℕ]
posℕ-from-posℤ {a⁺ — a⁻} a⁻<a⁺ =
  let n = ℕ.<-diff a⁻<a⁺
      pos[n] = ℕ.<-diff-pos a⁻<a⁺
      a⁺+0≃n+a⁻ =
        begin
          a⁺ + 0
        ≃⟨ AA.ident ⟩
          a⁺
        ≃˘⟨ ℕ.<-elim-diff a⁻<a⁺ ⟩
          a⁻ + n
        ≃⟨ AA.comm ⟩
          n + a⁻
        ∎
   in ℤ.≃posℕ-intro pos[n] (ℤ.≃₀-intro a⁺+0≃n+a⁻)

posℕ-from-negℤ : {a : ℤ} → S.Negative a → a ≃ -_ [posℕ]
posℕ-from-negℤ {a⁺ — a⁻} a⁺<a⁻ =
  let n = ℕ.<-diff a⁺<a⁻
      pos[n] = ℕ.<-diff-pos a⁺<a⁻
      a⁺+n≃0+a⁻ =
        begin
          a⁺ + n
        ≃⟨ ℕ.<-elim-diff a⁺<a⁻ ⟩
          a⁻
        ≃˘⟨ AA.ident ⟩
          0 + a⁻
        ∎
   in ℤ.≃posℕ-intro pos[n] (ℤ.≃₀-intro a⁺+n≃0+a⁻)

posℤ-from-posℕ : {a : ℤ} → a ≃ id [posℕ] → S.Positive a
posℤ-from-posℕ {a⁺ — a⁻} (ℤ.≃posℕ-intro {n} pos[n] (ℤ.≃₀-intro a⁺+0≃n+a⁻)) =
  let a⁻+n≃a⁺ =
        begin
          a⁻ + n
        ≃⟨ AA.comm ⟩
          n + a⁻
        ≃˘⟨ a⁺+0≃n+a⁻ ⟩
          a⁺ + 0
        ≃⟨ AA.ident ⟩
          a⁺
        ∎
   in ℕ.<-intro-diff pos[n] a⁻+n≃a⁺

negℤ-from-posℕ : {a : ℤ} → a ≃ -_ [posℕ] → S.Negative a
negℤ-from-posℕ {a⁺ — a⁻} (ℤ.≃posℕ-intro {n} pos[n] (ℤ.≃₀-intro a⁺+n≃0+a⁻)) =
  let a⁺+n≃a⁻ =
        begin
          a⁺ + n
        ≃⟨ a⁺+n≃0+a⁻ ⟩
          0 + a⁻
        ≃⟨ AA.ident ⟩
          a⁻
        ∎
   in ℕ.<-intro-diff pos[n] a⁺+n≃a⁻

from-ℕ-preserves-pos : {n : ℕ} → S.Positive n → S.Positive (n as ℤ)
from-ℕ-preserves-pos = ℕ.<-from-pos

neg-Positive : {a : ℤ} → S.Positive a → S.Negative (- a)
neg-Positive {a⁺ — a⁻} a⁻<a⁺ = a⁻<a⁺

neg-Negative : {a : ℤ} → S.Negative a → S.Positive (- a)
neg-Negative {a⁺ — a⁻} a⁺<a⁻ = a⁺<a⁻

instance
  sign-trichotomy : S.Trichotomy ℤ
  sign-trichotomy = S.trichotomy-intro sign-tri
    where
      sign-tri :
        (a : ℤ) → AA.ExactlyOneOfThree (a ≃ 0) (S.Positive a) (S.Negative a)
      sign-tri a@(a⁺ — a⁻) = AA.exactlyOneOfThree 1of3 ¬2of3
        where
          1of3 : AA.OneOfThree (a ≃ 0) (S.Positive a) (S.Negative a)
          1of3 with AA.ExactlyOneOfThree.at-least-one (ℕ.order-trichotomy a⁺ a⁻)
          1of3 | AA.1st a⁺<a⁻ = AA.3rd a⁺<a⁻
          1of3 | AA.2nd a⁺≃a⁻ = AA.1st (ℤ.zero-from-balanced a⁺≃a⁻)
          1of3 | AA.3rd a⁺>a⁻ = AA.2nd (Ord.>-flip a⁺>a⁻)

          ¬2of3 : ¬ AA.TwoOfThree (a ≃ 0) (S.Positive a) (S.Negative a)
          ¬2of3 = ¬-intro λ
            { (AA.1∧2 a≃0 pos[a]) → a≃0 ↯ (S.pos≄0 pos[a])
            ; (AA.1∧3 a≃0 neg[a]) → a≃0 ↯ (S.neg≄0 neg[a])
            ; (AA.2∧3 a⁻<a⁺ a⁺<a⁻) → ℕ.<-asymmetric a⁺<a⁻ a⁻<a⁺
            }

  +-preserves-pos : AA.Preserves S.Positive _+_
  +-preserves-pos = AA.preserves +-pres-pos
    where
      +-pres-pos : {a b : ℤ} → S.Positive a → S.Positive b → S.Positive (a + b)
      +-pres-pos {a⁺ — a⁻} {b⁺ — b⁻} a⁻<a⁺ b⁻<b⁺ = ℕ.<-compatible-+ a⁻<a⁺ b⁻<b⁺

instance
  positivity-common : S.PositivityCommon ℤ
  positivity-common = record {}

  sign-common : S.SignCommon ℤ
  sign-common =
    record { neg-Positive = neg-Positive ; neg-Negative = neg-Negative }

-- Include everything from the partial impl
private
  open import net.cruhland.axioms.Integers.SignPartialImpl PA ZB ZA ZN
    using (SignProperties)

  signProperties : SignProperties
  signProperties = record { from-ℕ-preserves-pos = from-ℕ-preserves-pos }

open SignProperties signProperties public
  hiding (from-ℕ-preserves-pos; positivity)
