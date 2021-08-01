import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_; -_; _-_; _*_)
open import net.cruhland.axioms.Peano using (PeanoArithmetic)
open import net.cruhland.axioms.Sign using (Negative; neg≄0; Positive; pos≄0)
import net.cruhland.models.Function
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using (_∨_; ∨-introᴸ; ∨-introᴿ; _↯_; no; yes)

module net.cruhland.axioms.Integers.MultiplicationPartialImpl
  (PA : PeanoArithmetic) where

open import net.cruhland.axioms.Integers.AdditionDecl PA using (Addition)
open import net.cruhland.axioms.Integers.BaseDecl PA using (Base)
import net.cruhland.axioms.Integers.LiteralImpl PA as LiteralImpl
import net.cruhland.axioms.Integers.MultiplicationDecl PA as MultiplicationDecl
open import net.cruhland.axioms.Integers.NegationDecl PA using (Negation)
open import net.cruhland.axioms.Integers.SignDecl PA using (Sign)

module _
    (ZB : Base)
    (ZA : Addition ZB)
    (ZN : Negation ZB ZA)
    (ZS : Sign ZB ZA ZN)
    where

  private module ℕ = PeanoArithmetic PA
  private module ℤ where
    open Addition ZA public
    open Base ZB public
    open LiteralImpl ZB public
    open MultiplicationDecl.MultiplicationPredefs ZB ZA ZN ZS public
    open Negation ZN public
    open Sign ZS public

  open ℕ using (ℕ)
  open ℤ using (_≃±1; ℤ)

  record MultiplicationProperties : Set where
    field
      {{star}} : Op.Star ℤ
      {{*-substitutive}} : AA.Substitutive² {A = ℤ} _*_ _≃_ _≃_
      {{*-associative}} : AA.Associative {A = ℤ} _*_
      {{*-commutative}} : AA.Commutative {A = ℤ} _*_
      {{*-compatible-ℕ}} : AA.Compatible₂ {A = ℕ} (_as ℤ) _*_ _*_ _≃_
      {{*-identity}} : AA.Identity² {A = ℤ} _*_ 1

      {{*-distributive}} : AA.Distributive² {A = ℤ} _*_ _+_
      {{*-comm-with-neg}} : AA.FnOpCommutative² -_ _*_

    neg-mult : {a : ℤ} → -1 * a ≃ - a
    neg-mult {a} =
      begin
        -1 * a
      ≃⟨⟩
        (- 1) * a
      ≃˘⟨ AA.fnOpComm ⟩
        - (1 * a)
      ≃⟨ AA.subst₁ AA.ident ⟩
        - a
      ∎

    instance
      *-distributive-subᴸ : AA.Distributive AA.handᴸ _*_ _-_
      *-distributive-subᴸ = AA.distributive *-distrib-subᴸ
        where
          *-distrib-subᴸ : {a b c : ℤ} → c * (a - b) ≃ c * a - c * b
          *-distrib-subᴸ {a} {b} {c} =
            begin
              c * (a - b)
            ≃⟨ AA.subst₂ ℤ.sub-defn ⟩
              c * (a + (- b))
            ≃⟨ AA.distrib ⟩
              c * a + c * (- b)
            ≃˘⟨ AA.subst₂ AA.fnOpComm ⟩
              c * a + (- (c * b))
            ≃˘⟨ ℤ.sub-defn ⟩
              c * a - c * b
            ∎

      *-distributive-subᴿ : AA.Distributive AA.handᴿ _*_ _-_
      *-distributive-subᴿ = AA.distributiveᴿ-from-distributiveᴸ

      *-distributive-sub : AA.Distributive² _*_ _-_
      *-distributive-sub = AA.distributive²

      private
        *-absorptiveᴸ : AA.Absorptive AA.handᴸ _*_ 0
        *-absorptiveᴸ = AA.absorptive *-absorbᴸ
          where
            *-absorbᴸ : {a : ℤ} → 0 * a ≃ 0
            *-absorbᴸ {a} =
              begin
                0 * a
              ≃˘⟨ AA.subst₂ ℤ.sub-same≃zero ⟩
                (1 - 1) * a
              ≃⟨ AA.distrib ⟩
                1 * a - 1 * a
              ≃⟨ ℤ.sub-same≃zero ⟩
                0
              ∎

        *-absorptiveᴿ : AA.Absorptive AA.handᴿ _*_ 0
        *-absorptiveᴿ = AA.absorptiveᴿ-from-absorptiveᴸ {A = ℤ}

      *-absorptive : AA.Absorptive² _*_ 0
      *-absorptive = AA.absorptive² {A = ℤ}

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
            let -[-b]≃±1 = AA.subst₁ (Eq.sym ℤ.neg-involutive) b≃±1
                -b≃±1 = ℤ.≃±1-absorbs-neg -[-b]≃±1
                -b≃ab =
                  begin
                    - b
                  ≃˘⟨ neg-mult ⟩
                    -1 * b
                  ≃˘⟨ AA.subst₂ a≃-1 ⟩
                    a * b
                  ∎
             in AA.subst₁ -b≃ab -b≃±1

      *-preserves-Positive : AA.Preserves Positive _*_
      *-preserves-Positive = AA.preserves *-pres-pos
        where
          *-pres-pos : {a b : ℤ} → Positive a → Positive b → Positive (a * b)
          *-pres-pos {a} {b} pos[a] pos[b] =
            let ℤ.≃posℕ-intro {n} pos[n] a≃n = ℤ.posℕ-from-posℤ pos[a]
                ℤ.≃posℕ-intro {m} pos[m] b≃m = ℤ.posℕ-from-posℤ pos[b]
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
             in ℤ.posℤ-from-posℕ (ℤ.≃posℕ-intro pos[nm] ab≃nm)

    PosOrNeg-from-nonzero : {a : ℤ} → a ≄ 0 → ℤ.PosOrNeg a
    PosOrNeg-from-nonzero {a} a≄0
      with AA.ExactlyOneOfThree.at-least-one (ℤ.trichotomy a)
    ... | AA.1st neg[a] =
      let ℤ.≃posℕ-intro pos[n] a≃-n = ℤ.posℕ-from-negℤ neg[a]
          a≃-1*n = Eq.trans a≃-n (Eq.sym neg-mult)
       in ℤ.PosOrNeg-intro pos[n] (ℤ.≃-1-intro Eq.refl) a≃-1*n
    ... | AA.2nd a≃0 =
      a≃0 ↯ a≄0
    ... | AA.3rd pos[a] =
      let ℤ.≃posℕ-intro pos[n] a≃n = ℤ.posℕ-from-posℤ pos[a]
          a≃1*n = Eq.trans a≃n (Eq.sym AA.ident)
       in ℤ.PosOrNeg-intro pos[n] (ℤ.≃+1-intro Eq.refl) a≃1*n

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
       in pos≄0 (ℤ.posℤ-from-posℕ (ℤ.≃posℕ-intro pos[n] a≃n))
    nonzero-from-PosOrNeg
        {a} (ℤ.PosOrNeg-intro {n} {s} pos[n] (ℤ.≃-1-intro s≃-1) a≃sn) =
      let a≃-n =
            begin
              a
            ≃⟨ a≃sn ⟩
              s * (n as ℤ)
            ≃⟨ AA.subst₂ s≃-1 ⟩
              -1 * (n as ℤ)
            ≃⟨ neg-mult ⟩
              - (n as ℤ)
            ∎
       in neg≄0 (ℤ.negℤ-from-posℕ (ℤ.≃posℕ-intro pos[n] a≃-n))

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
      zero-product : AA.ZeroProduct 0 _*_
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

      neg-compatible-+ : AA.Compatible₂ -_ _+_ _+_ _≃_
      neg-compatible-+ = AA.compatible₂ neg-compat-+
        where
          neg-compat-+ : {a b : ℤ} → - (a + b) ≃ (- a) + (- b)
          neg-compat-+ {a} {b} =
            begin
              - (a + b)
            ≃˘⟨ neg-mult ⟩
              -1 * (a + b)
            ≃⟨ AA.distrib ⟩
              -1 * a + -1 * b
            ≃⟨ AA.subst₂ neg-mult ⟩
              (- a) + -1 * b
            ≃⟨ AA.subst₂ neg-mult ⟩
              (- a) + (- b)
            ∎

    neg-sub-swap : {a b : ℤ} → - (a - b) ≃ b - a
    neg-sub-swap {a} {b} =
      begin
        - (a - b)
      ≃⟨ AA.subst₁ ℤ.sub-defn ⟩
        - (a + (- b))
      ≃⟨ AA.compat₂ ⟩
        (- a) + (- (- b))
      ≃⟨ AA.subst₂ ℤ.neg-involutive ⟩
        (- a) + b
      ≃⟨ AA.comm ⟩
        b + (- a)
      ≃˘⟨ ℤ.sub-defn ⟩
        b - a
      ∎

    sub-sign-swap : {a b : ℤ} → Negative (a - b) → Positive (b - a)
    sub-sign-swap neg[a-b] =
      let pos[-[a-b]] = ℤ.neg-Negative neg[a-b]
       in AA.subst₁ neg-sub-swap pos[-[a-b]]
