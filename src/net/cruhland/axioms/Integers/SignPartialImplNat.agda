import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Integers.AdditionDecl using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl using (Base)
open import net.cruhland.axioms.Integers.NegationDecl using (Negation)
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign
  using (Negative; Negativity; Positive; Positivity; pos≄0)
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_)

module net.cruhland.axioms.Integers.SignPartialImplNat
  (PA : PeanoArithmetic)
  (ZB : Base PA)
  (ZA : Addition PA ZB)
  (ZN : Negation PA ZB ZA)
  where

import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
import net.cruhland.axioms.Integers.SignDecl PA as SignDecl

private module ℕ = PeanoArithmetic PA
private module ℤ where
  open Addition ZA public
  open Base ZB public
  open LiteralImpl ZB public
  open Negation ZN public
  open SignDecl.SignPredefs ZB ZA ZN public

open ℕ using (ℕ)
open ℤ using (ℤ; _≃_[posℕ])

nonzero-from-≃id[posℕ] : ∀ {a} → a ≃ id [posℕ] → a ≄ 0
nonzero-from-≃id[posℕ] {a} (ℤ.≃posℕ-intro {n} pos[n] a≃n) =
  Eq.≄-intro λ a≃0 →
    let n:ℤ≃0:ℤ =
          begin
            (n as ℤ)
          ≃˘⟨ a≃n ⟩
            a
          ≃⟨ a≃0 ⟩
            0
          ≃⟨⟩
            (0 as ℤ)
          ∎
        n≃0 = AA.inject n:ℤ≃0:ℤ
        n≄0 = pos≄0 pos[n]
     in n≃0 ↯ n≄0

instance
  pos-substitutive : AA.Substitutive₁ (_≃ id [posℕ]) _≃_ _⟨→⟩_
  pos-substitutive = AA.substitutive₁ pos-subst
    where
      pos-subst : ∀ {a b} → a ≃ b → a ≃ id [posℕ] → b ≃ id [posℕ]
      pos-subst a≃b (ℤ.≃posℕ-intro pos[n] a≃n) =
        ℤ.≃posℕ-intro pos[n] (Eq.trans (Eq.sym a≃b) a≃n)

  positivity : Positivity {A = ℤ} 0
  positivity =
    record { Positive = _≃ id [posℕ] ; pos≄0 = nonzero-from-≃id[posℕ] }

nonzero-from-≃neg[posℕ] : ∀ {a} → a ≃ -_ [posℕ] → a ≄ 0
nonzero-from-≃neg[posℕ] {a} (ℤ.≃posℕ-intro {n} pos[n] a≃-n) =
  Eq.≄-intro λ a≃0 →
    let n:ℤ≃0:ℤ =
          begin
            (n as ℤ)
          ≃˘⟨ ℤ.neg-involutive ⟩
            - (- (n as ℤ))
          ≃˘⟨ AA.subst₁ a≃-n ⟩
            - a
          ≃⟨ AA.subst₁ a≃0 ⟩
            - 0
          ≃⟨ ℤ.neg-zero ⟩
            0
          ≃⟨⟩
            (0 as ℤ)
          ∎
        n≃0 = AA.inject n:ℤ≃0:ℤ
        n≄0 = pos≄0 pos[n]
     in n≃0 ↯ n≄0

instance
  negative-substitutive : AA.Substitutive₁ (_≃ -_ [posℕ]) _≃_ _⟨→⟩_
  negative-substitutive = AA.substitutive₁ neg-subst
    where
      neg-subst : ∀ {a b} → a ≃ b → a ≃ -_ [posℕ] → b ≃ -_ [posℕ]
      neg-subst a≃b (ℤ.≃posℕ-intro pos[n] a≃n) =
        ℤ.≃posℕ-intro pos[n] (Eq.trans (Eq.sym a≃b) a≃n)

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
from-ℕ-preserves-pos pos[n] = ℤ.≃posℕ-intro pos[n] Eq.refl

neg-Positive : {a : ℤ} → Positive a → Negative (- a)
neg-Positive (ℤ.≃posℕ-intro pos[n] a≃n) =
  let -a≃-n = AA.subst₁ a≃n
   in ℤ.≃posℕ-intro pos[n] -a≃-n

neg-Negative : {a : ℤ} → Negative a → Positive (- a)
neg-Negative {a} (ℤ.≃posℕ-intro {n} pos[n] a≃-n) =
  let -a≃n =
        begin
          - a
        ≃⟨ AA.subst₁ a≃-n ⟩
          - (- (n as ℤ))
        ≃⟨ ℤ.neg-involutive ⟩
          (n as ℤ)
        ∎
   in ℤ.≃posℕ-intro pos[n] -a≃n

instance
  +-preserves-pos : AA.Preserves Positive _+_
  +-preserves-pos = AA.preserves +-pres-pos
    where
      +-pres-pos : {a b : ℤ} → Positive a → Positive b → Positive (a + b)
      +-pres-pos {a} {b}
          (ℤ.≃posℕ-intro {n} pos[n] a≃n) (ℤ.≃posℕ-intro {m} pos[m] b≃m) =
        let pos[n+m] = AA.pres pos[n] pos[m]
            a+b≃n+m =
              begin
                a + b
              ≃⟨ AA.subst₂ a≃n ⟩
                (n as ℤ) + b
              ≃⟨ AA.subst₂ b≃m ⟩
                (n as ℤ) + (m as ℤ)
              ≃˘⟨ AA.compat₂ ⟩
                (n + m as ℤ)
              ∎
         in ℤ.≃posℕ-intro pos[n+m] a+b≃n+m

-- Include everything from the common partial impl
open import net.cruhland.axioms.Integers.SignPartialImpl PA ZB ZA ZN
  using (SignProperties)

private
  signProperties : SignProperties
  signProperties = record { from-ℕ-preserves-pos = from-ℕ-preserves-pos }

open SignProperties signProperties public
  hiding (from-ℕ-preserves-pos; positivity)
