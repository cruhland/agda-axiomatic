import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators using (-_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_⟨→⟩_; id)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using (_∨_; ∨-introᴸ; ∨-introᴿ; _↯_; no; yes)

module net.cruhland.axioms.Integers.SignPartialImpl (PA : PeanoArithmetic) where

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

record SignProperties
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZM : Multiplication ZB ZA ZN)
    : Set₁ where
  private
    open module ℤ = IntegerPredefs ZB ZA ZN ZM using (ℤ; _≃±1; _≃_[posℕ])

  field
    {{positivity}} : S.Positivity ℤ
    {{negativity}} : S.Negativity ℤ
    {{sign-trichotomy}} : S.Trichotomy ℤ
    neg-Negative : {a : ℤ} → S.Negative a → S.Positive (- a)

    posℕ-from-posℤ : {a : ℤ} → S.Positive a → a ≃ id [posℕ]
    posℕ-from-negℤ : {a : ℤ} → S.Negative a → a ≃ -_ [posℕ]
    posℤ-from-posℕ : {a : ℤ} → a ≃ id [posℕ] → S.Positive a
    negℤ-from-posℕ : {a : ℤ} → a ≃ -_ [posℕ] → S.Negative a

    from-ℕ-preserves-pos : {n : ℕ} → S.Positive n → S.Positive (n as ℤ)

  instance
    ≃±1-substitutive : AA.Substitutive₁ _≃±1 _≃_ _⟨→⟩_
    ≃±1-substitutive = AA.substitutive₁ ≃±1-subst
      where
        ≃±1-subst : {s₁ s₂ : ℤ} → s₁ ≃ s₂ → s₁ ≃±1 → s₂ ≃±1
        ≃±1-subst s₁≃s₂ (ℤ.≃+1-intro s₁≃1) =
          let s₂≃1 = Eq.trans (Eq.sym s₁≃s₂) s₁≃1
           in ℤ.≃+1-intro s₂≃1
        ≃±1-subst s₁≃s₂ (ℤ.≃-1-intro s₁≃-1) =
          let s₂≃-1 = Eq.trans (Eq.sym s₁≃s₂) s₁≃-1
           in ℤ.≃-1-intro s₂≃-1

  ≃±1-absorbs-neg : {a : ℤ} → - a ≃±1 → a ≃±1
  ≃±1-absorbs-neg {a} (ℤ.≃+1-intro -a≃1) =
    let a≃-1 =
          begin
            a
          ≃˘⟨ AA.inv-involutive ⟩
            - (- a)
          ≃⟨ AA.subst₁ -a≃1 ⟩
            - 1
          ≃⟨⟩
            -1
          ∎
     in ℤ.≃-1-intro a≃-1
  ≃±1-absorbs-neg {a} (ℤ.≃-1-intro -a≃-1) =
    let a≃1 = AA.inject -a≃-1
     in ℤ.≃+1-intro a≃1

  1-Positive : S.Positive {A = ℤ} 1
  1-Positive = from-ℕ-preserves-pos (ℕ.Pos-intro-≄0 ℕ.step≄zero)

  instance
    *-preserves-≃±1 : AA.Preserves _≃±1 _*_
    *-preserves-≃±1 = AA.preserves *-pres-≃±1
      where
        *-pres-≃±1 : {a b : ℤ} → a ≃±1 → b ≃±1 → a * b ≃±1
        *-pres-≃±1 {a} {b} (ℤ.≃+1-intro a≃1) b≃±1 =
          let b≃ab =
                begin
                  b
                ≃˘⟨ AA.ident ⟩
                  1 * b
                ≃˘⟨ AA.subst₂ a≃1 ⟩
                  a * b
                ∎
           in AA.subst₁ b≃ab b≃±1
        *-pres-≃±1 {a} {b} (ℤ.≃-1-intro a≃-1) b≃±1 =
          let -[-b]≃±1 = AA.subst₁ (Eq.sym AA.inv-involutive) b≃±1
              -b≃±1 = ≃±1-absorbs-neg -[-b]≃±1
              -b≃ab =
                begin
                  - b
                ≃˘⟨ ℤ.neg-mult ⟩
                  -1 * b
                ≃˘⟨ AA.subst₂ a≃-1 ⟩
                  a * b
                ∎
           in AA.subst₁ -b≃ab -b≃±1

    *-preserves-Positive : AA.Preserves S.Positive _*_
    *-preserves-Positive = AA.preserves *-pres-pos
      where
        *-pres-pos :
          {a b : ℤ} → S.Positive a → S.Positive b → S.Positive (a * b)
        *-pres-pos {a} {b} pos[a] pos[b] =
          let ℤ.≃posℕ-intro {n} pos[n] a≃n = posℕ-from-posℤ pos[a]
              ℤ.≃posℕ-intro {m} pos[m] b≃m = posℕ-from-posℤ pos[b]
              pos[nm] = AA.pres pos[n] pos[m]
              ab≃nm =
                begin
                  a * b
                ≃⟨ AA.subst₂ a≃n ⟩
                  (n as ℤ) * b
                ≃⟨ AA.subst₂ b≃m ⟩
                  (n as ℤ) * (m as ℤ)
                ≃˘⟨ AA.compat₂ ⟩
                  (n * m as ℤ)
                ∎
           in posℤ-from-posℕ (ℤ.≃posℕ-intro pos[nm] ab≃nm)

  PosOrNeg-from-nonzero : {a : ℤ} → a ≄ 0 → ℤ.PosOrNeg a
  PosOrNeg-from-nonzero {a} a≄0
    with AA.ExactlyOneOfThree.at-least-one (S.trichotomy a)
  ... | AA.1st a≃0 =
    a≃0 ↯ a≄0
  ... | AA.2nd pos[a] =
    let ℤ.≃posℕ-intro pos[n] a≃n = posℕ-from-posℤ pos[a]
        a≃1*n = Eq.trans a≃n (Eq.sym AA.ident)
     in ℤ.PosOrNeg-intro pos[n] (ℤ.≃+1-intro Eq.refl) a≃1*n
  ... | AA.3rd neg[a] =
    let ℤ.≃posℕ-intro pos[n] a≃-n = posℕ-from-negℤ neg[a]
        a≃-1*n = Eq.trans a≃-n (Eq.sym ℤ.neg-mult)
     in ℤ.PosOrNeg-intro pos[n] (ℤ.≃-1-intro Eq.refl) a≃-1*n

  nonzero-from-PosOrNeg : {a : ℤ} → ℤ.PosOrNeg a → a ≄ 0
  nonzero-from-PosOrNeg
      {a} (ℤ.PosOrNeg-intro {n} {s} pos[n] (ℤ.≃+1-intro s≃1) a≃sn) =
    let a≃n =
          begin
            a
          ≃⟨ a≃sn ⟩
            s * (n as ℤ)
          ≃⟨ AA.subst₂ s≃1 ⟩
            1 * (n as ℤ)
          ≃⟨ AA.ident ⟩
            (n as ℤ)
          ∎
     in S.pos≄0 (posℤ-from-posℕ (ℤ.≃posℕ-intro pos[n] a≃n))
  nonzero-from-PosOrNeg
      {a} (ℤ.PosOrNeg-intro {n} {s} pos[n] (ℤ.≃-1-intro s≃-1) a≃sn) =
    let a≃-n =
          begin
            a
          ≃⟨ a≃sn ⟩
            s * (n as ℤ)
          ≃⟨ AA.subst₂ s≃-1 ⟩
            -1 * (n as ℤ)
          ≃⟨ ℤ.neg-mult ⟩
            - (n as ℤ)
          ∎
     in S.neg≄0 (negℤ-from-posℕ (ℤ.≃posℕ-intro pos[n] a≃-n))

  *-neither-zero : {a b : ℤ} → a ≄ 0 → b ≄ 0 → a * b ≄ 0
  *-neither-zero {a} {b} a≄0 b≄0 =
    let ℤ.PosOrNeg-intro {na} {sa} pos[na] sa≃±1 a≃sa*na =
          PosOrNeg-from-nonzero a≄0
        ℤ.PosOrNeg-intro {nb} {sb} pos[nb] sb≃±1 b≃sb*nb =
          PosOrNeg-from-nonzero b≄0
        pos[na*nb] = AA.pres pos[na] pos[nb]
        sa*sb≃±1 = AA.pres sa≃±1 sb≃±1
        ab≃[sa*sb]*[na*nb] =
          begin
            a * b
          ≃⟨ AA.subst₂ a≃sa*na ⟩
            (sa * (na as ℤ)) * b
          ≃⟨ AA.subst₂ b≃sb*nb ⟩
            (sa * (na as ℤ)) * (sb * (nb as ℤ))
          ≃⟨ AA.transpose ⟩
            (sa * sb) * ((na as ℤ) * (nb as ℤ))
          ≃˘⟨ AA.subst₂ AA.compat₂ ⟩
            (sa * sb) * (na * nb as ℤ)
          ∎
        ±ab = ℤ.PosOrNeg-intro pos[na*nb] sa*sb≃±1 ab≃[sa*sb]*[na*nb]
     in nonzero-from-PosOrNeg ±ab

  instance
    zero-product : AA.ZeroProduct _*_
    zero-product = AA.zeroProduct *-either-zero
      where
        *-either-zero : {a b : ℤ} → a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0
        *-either-zero {a} {b} ab≃0 with a ≃? 0
        ... | yes a≃0 = ∨-introᴸ a≃0
        ... | no a≄0 with b ≃? 0
        ... | yes b≃0 = ∨-introᴿ b≃0
        ... | no b≄0 = ab≃0 ↯ *-neither-zero a≄0 b≄0

    private
      *-cancellativeᴸ : AA.Cancellative AA.handᴸ _*_ _≃_ _≃_ (_≄ 0)
      *-cancellativeᴸ = AA.cancellative *-cancelᴸ
        where
          *-cancelᴸ : {a : ℤ} {{_ : a ≄ 0}} {b c : ℤ} → a * b ≃ a * c → b ≃ c
          *-cancelᴸ {a} {{a≄0}} {b} {c} ab≃ac with
            (let a[b-c]≃0 =
                   begin
                     a * (b - c)
                   ≃⟨ AA.distrib ⟩
                     a * b - a * c
                   ≃⟨ AA.subst₂ ab≃ac ⟩
                     a * c - a * c
                   ≃⟨ ℤ.sub-same≃zero ⟩
                     0
                   ∎
              in AA.zero-prod a[b-c]≃0)
          ... | ∨-introᴸ a≃0 = a≃0 ↯ a≄0
          ... | ∨-introᴿ b-c≃0 = ℤ.≃-from-zero-sub b-c≃0

      *-cancellativeᴿ : AA.Cancellative AA.handᴿ _*_ _≃_ _≃_ (_≄ 0)
      *-cancellativeᴿ = AA.cancelᴿ-from-cancelᴸ-comm {A = ℤ}

    *-cancellative : AA.Cancellative² _*_ _≃_ _≃_ (_≄ 0)
    *-cancellative = AA.cancellative² {A = ℤ}

  sub-sign-swap : {a b : ℤ} → S.Negative (a - b) → S.Positive (b - a)
  sub-sign-swap neg[a-b] =
    let pos[-[a-b]] = neg-Negative neg[a-b]
     in AA.subst₁ ℤ.neg-sub-swap pos[-[a-b]]
