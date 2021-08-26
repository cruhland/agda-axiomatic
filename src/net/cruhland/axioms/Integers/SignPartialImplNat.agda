import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (_+_; -_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_↯_)

module net.cruhland.axioms.Integers.SignPartialImplNat
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
open import net.cruhland.axioms.Integers.MultiplicationDecl PA
  using (Multiplication)
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
import net.cruhland.axioms.Integers.SignDecl PA as SignDecl

private
  open module ℕ = PeanoArithmetic PA using (ℕ)
  module IntegerPredefs
      (ZB : Base)
      (ZA : Addition ZB)
      (ZN : Negation ZB ZA)
      (ZM : Multiplication ZB ZA ZN)
      where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open Multiplication ZM public
    open Negation ZN public
    open SignDecl.SignPredefs ZB ZA ZN ZM public

module SignPredefs
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZM : Multiplication ZB ZA ZN)
    where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN ZM using (ℤ; _≃_[posℕ])

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
          n≄0 = S.pos≄0 pos[n]
       in n≃0 ↯ n≄0

  instance
    pos-substitutive : AA.Substitutive₁ (_≃ id [posℕ]) _≃_ _⟨→⟩_
    pos-substitutive = AA.substitutive₁ pos-subst
      where
        pos-subst : ∀ {a b} → a ≃ b → a ≃ id [posℕ] → b ≃ id [posℕ]
        pos-subst a≃b (ℤ.≃posℕ-intro pos[n] a≃n) =
          ℤ.≃posℕ-intro pos[n] (Eq.trans (Eq.sym a≃b) a≃n)

    positivity : S.Positivity ℤ
    positivity =
      record { Positive = _≃ id [posℕ] ; pos≄0 = nonzero-from-≃id[posℕ] }

  nonzero-from-≃neg[posℕ] : ∀ {a} → a ≃ -_ [posℕ] → a ≄ 0
  nonzero-from-≃neg[posℕ] {a} (ℤ.≃posℕ-intro {n} pos[n] a≃-n) =
    Eq.≄-intro λ a≃0 →
      let n:ℤ≃0:ℤ =
            begin
              (n as ℤ)
            ≃˘⟨ AA.inv-involutive ⟩
              - (- (n as ℤ))
            ≃˘⟨ AA.subst₁ a≃-n ⟩
              - a
            ≃⟨ AA.subst₁ a≃0 ⟩
              - 0
            ≃⟨ AA.inv-ident ⟩
              0
            ≃⟨⟩
              (0 as ℤ)
            ∎
          n≃0 = AA.inject n:ℤ≃0:ℤ
          n≄0 = S.pos≄0 pos[n]
       in n≃0 ↯ n≄0

  instance
    negative-substitutive : AA.Substitutive₁ (_≃ -_ [posℕ]) _≃_ _⟨→⟩_
    negative-substitutive = AA.substitutive₁ neg-subst
      where
        neg-subst : ∀ {a b} → a ≃ b → a ≃ -_ [posℕ] → b ≃ -_ [posℕ]
        neg-subst a≃b (ℤ.≃posℕ-intro pos[n] a≃n) =
          ℤ.≃posℕ-intro pos[n] (Eq.trans (Eq.sym a≃b) a≃n)

    negativity : S.Negativity ℤ
    negativity =
      record { Negative = _≃ -_ [posℕ] ; neg≄0 = nonzero-from-≃neg[posℕ] }

record SignPropertiesNat
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZM : Multiplication ZB ZA ZN)
    : Set where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN ZM using (ℤ; _≃_[posℕ])
    open SignPredefs ZB ZA ZN ZM

  field
    {{sign-trichotomy}} : S.Trichotomy ℤ

  posℕ-from-posℤ : {a : ℤ} → S.Positive a → a ≃ id [posℕ]
  posℕ-from-posℤ = id

  posℕ-from-negℤ : {a : ℤ} → S.Negative a → a ≃ -_ [posℕ]
  posℕ-from-negℤ = id

  posℤ-from-posℕ : {a : ℤ} → a ≃ id [posℕ] → S.Positive a
  posℤ-from-posℕ = id

  negℤ-from-posℕ : {a : ℤ} → a ≃ -_ [posℕ] → S.Negative a
  negℤ-from-posℕ = id

  from-ℕ-preserves-pos : {n : ℕ} → S.Positive n → S.Positive (n as ℤ)
  from-ℕ-preserves-pos pos[n] = ℤ.≃posℕ-intro pos[n] Eq.refl

  neg-Positive : {a : ℤ} → S.Positive a → S.Negative (- a)
  neg-Positive (ℤ.≃posℕ-intro pos[n] a≃n) =
    let -a≃-n = AA.subst₁ a≃n
     in ℤ.≃posℕ-intro pos[n] -a≃-n

  neg-Negative : {a : ℤ} → S.Negative a → S.Positive (- a)
  neg-Negative {a} (ℤ.≃posℕ-intro {n} pos[n] a≃-n) =
    let -a≃n =
          begin
            - a
          ≃⟨ AA.subst₁ a≃-n ⟩
            - (- (n as ℤ))
          ≃⟨ AA.inv-involutive ⟩
            (n as ℤ)
          ∎
     in ℤ.≃posℕ-intro pos[n] -a≃n

  instance
    +-preserves-pos : AA.Preserves S.Positive _+_
    +-preserves-pos = AA.preserves +-pres-pos
      where
        +-pres-pos : {a b : ℤ} → S.Positive a → S.Positive b → S.Positive (a + b)
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

    +-preserves-neg : AA.Preserves S.Negative _+_
    +-preserves-neg = AA.preserves +-pres-neg
      where
        +-pres-neg : {a b : ℤ} → S.Negative a → S.Negative b → S.Negative (a + b)
        +-pres-neg {a} {b}
            (ℤ.≃posℕ-intro {n} pos[n] a≃-n) (ℤ.≃posℕ-intro {m} pos[m] b≃-m) =
          let pos[n+m] = AA.pres pos[n] pos[m]
              a+b≃-[n+m] =
                begin
                  a + b
                ≃⟨ AA.subst₂ a≃-n ⟩
                  - (n as ℤ) + b
                ≃⟨ AA.subst₂ b≃-m ⟩
                  - (n as ℤ) + - (m as ℤ)
                ≃˘⟨ AA.compat₂ ⟩
                  - ((n as ℤ) + (m as ℤ))
                ≃˘⟨ AA.subst₁ AA.compat₂ ⟩
                  - (n + m as ℤ)
                ∎
           in ℤ.≃posℕ-intro pos[n+m] a+b≃-[n+m]

  -- Include everything from the common partial impl
  private
    open import net.cruhland.axioms.Integers.SignPartialImpl PA
      using (SignProperties)

    signProperties : SignProperties ZB ZA ZN ZM
    signProperties = record
      { from-ℕ-preserves-pos = from-ℕ-preserves-pos
      ; neg-Negative = neg-Negative
      ; posℕ-from-posℤ = posℕ-from-posℤ
      ; posℕ-from-negℤ = posℕ-from-negℤ
      ; posℤ-from-posℕ = posℤ-from-posℕ
      ; negℤ-from-posℕ = negℤ-from-posℕ
      }

  open SignProperties signProperties public
    hiding ( from-ℕ-preserves-pos; negativity; neg-Negative; negℤ-from-posℕ
           ; positivity; posℕ-from-negℤ; posℕ-from-posℤ; posℤ-from-posℕ)
