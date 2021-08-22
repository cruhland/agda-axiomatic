import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Ordering as Ord using (_<_)
open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
import net.cruhland.axioms.Peano.Literals as Literals
open import net.cruhland.axioms.Peano.Ordering using (Ordering)
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (it)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using (∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; _↯_)

module net.cruhland.axioms.Peano.Multiplication where

private
  module Predefs
      (PB : PeanoBase)
      (PS : ℕSign PB)
      (PA : Addition PB PS)
      (PO : Ordering PB PS PA)
      where
    open Addition PA public
    open Literals PB public
    open ℕSign PS public
    open Ordering PO public
    open PeanoBase PB public
    open PeanoInspect PB public

record Multiplication
    (PB : PeanoBase)
    (PS : ℕSign PB)
    (PA : Addition PB PS)
    (PO : Ordering PB PS PA)
    : Set where
  private open module ℕ = Predefs PB PS PA PO using (ℕ; step)

  field
    {{star}} : Op.Star ℕ
    {{*-substitutiveᴸ}} : AA.Substitutive₂ AA.handᴸ _*_ _≃_ _≃_
    {{*-absorptiveᴸ}} : AA.Absorptive AA.handᴸ (AA.tc₂ _*_)
    *-stepᴸ : ∀ {n m} → step n * m ≃ n * m + m

  instance
    *-absorptiveᴿ : AA.Absorptive AA.handᴿ (AA.tc₂ _*_)
    *-absorptiveᴿ = AA.absorptive *-zeroᴿ
      where
        *-zeroᴿ : ∀ {n} → n * 0 ≃ 0
        *-zeroᴿ {n} = ℕ.ind P P0 Ps n
          where
            P = λ x → x * 0 ≃ 0
            P0 = AA.absorbᴸ

            Ps : ℕ.step-case P
            Ps {k} Pk =
              begin
                step k * 0
              ≃⟨ *-stepᴸ ⟩
                k * 0 + 0
              ≃⟨ AA.ident ⟩
                k * 0
              ≃⟨ Pk ⟩
                0
              ∎

    *-absorptive² : AA.Absorptive² (AA.tc₂ _*_)
    *-absorptive² = AA.absorptive²

  *-stepᴿ : ∀ {n m} → n * step m ≃ n * m + n
  *-stepᴿ {n} {m} = ℕ.ind P P0 Ps n
    where
      P = λ x → x * step m ≃ x * m + x

      P0 =
        begin
          0 * step m
        ≃⟨ AA.absorb ⟩
          0
        ≃˘⟨ AA.absorb ⟩
          0 * m
        ≃˘⟨ AA.ident ⟩
          0 * m + 0
        ∎

      Ps : ℕ.step-case P
      Ps {k} Pk =
        begin
          step k * step m
        ≃⟨ *-stepᴸ ⟩
          k * step m + step m
        ≃⟨ AA.subst₂ Pk ⟩
          k * m + k + step m
        ≃⟨ AA.substᴿ-with-assoc (Eq.trans AA.comm AA.fnOpCommSwap) ⟩
          k * m + m + step k
        ≃˘⟨ AA.subst₂ *-stepᴸ ⟩
          step k * m + step k
        ∎

  instance
    *-commutative : AA.Commutative _*_
    *-commutative = AA.commutative *-comm
      where
        *-comm : ∀ {n m} → n * m ≃ m * n
        *-comm {n} {m} = ℕ.ind P P0 Ps n
          where
            P = λ x → x * m ≃ m * x
            P0 = Eq.trans AA.absorb (Eq.sym AA.absorb)

            Ps : ℕ.step-case P
            Ps {k} Pk =
              begin
                step k * m
              ≃⟨ *-stepᴸ ⟩
                k * m + m
              ≃⟨ AA.subst₂ Pk ⟩
                m * k + m
              ≃˘⟨ *-stepᴿ ⟩
                m * step k
              ∎

    *-identityᴸ : AA.Identity AA.handᴸ _*_ 1
    *-identityᴸ = AA.identity *-oneᴸ
      where
        *-oneᴸ : {n : ℕ} → 1 * n ≃ n
        *-oneᴸ {n} =
          begin
            1 * n
          ≃⟨ *-stepᴸ ⟩
            0 * n + n
          ≃⟨ AA.subst₂ AA.absorb ⟩
            0 + n
          ≃⟨ AA.ident ⟩
            n
          ∎

    *-identityᴿ : AA.Identity AA.handᴿ _*_ 1
    *-identityᴿ = AA.identityᴿ-from-identityᴸ

    zero-product : AA.ZeroProduct _*_
    zero-product = AA.zeroProduct *-either-zero
      where
        *-either-zero : ∀ {n m} → n * m ≃ 0 → n ≃ 0 ∨ m ≃ 0
        *-either-zero {n} {m} n*m≃0 with ℕ.case n
        ... | ℕ.case-zero n≃0 =
          ∨-introᴸ n≃0
        ... | ℕ.case-step (ℕ.pred-intro p n≃sp) =
          let p*m+m≃0 =
                begin
                  p * m + m
                ≃˘⟨ *-stepᴸ ⟩
                  step p * m
                ≃˘⟨ AA.subst₂ n≃sp ⟩
                  n * m
                ≃⟨ n*m≃0 ⟩
                  0
                ∎
              ∧-intro _ m≃0 = ℕ.+-both-zero p*m+m≃0
           in ∨-introᴿ m≃0

    *-preserves-Positive : AA.Preserves S.Positive _*_
    *-preserves-Positive = AA.preserves *-pres-pos
      where
        *-pres-pos :
          {n m : ℕ} → S.Positive n → S.Positive m → S.Positive (n * m)
        *-pres-pos pos[n] pos[m] =
          let instance n≄0 = S.pos≄0 pos[n]
              instance m≄0 = S.pos≄0 pos[m]
           in ℕ.Pos-intro-≄0 AA.nonzero-prod

    *-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _*_ _≃_ _≃_
    *-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm

    *-substitutive : AA.Substitutive² _*_ _≃_ _≃_
    *-substitutive = AA.substitutive²

    *-distributive-+ᴸ : AA.Distributive AA.handᴸ (AA.tc₂ _*_) _+_
    *-distributive-+ᴸ = AA.distributive *-distrib-+ᴸ
      where
        *-distrib-+ᴸ : ∀ {a b c} → a * (b + c) ≃ a * b + a * c
        *-distrib-+ᴸ {a} {b} {c} = ℕ.ind P P0 Ps c
          where
            P = λ x → a * (b + x) ≃ a * b + a * x
            P0 =
              begin
                a * (b + 0)
              ≃⟨ AA.subst₂ AA.ident ⟩
                a * b
              ≃˘⟨ AA.ident ⟩
                a * b + 0
              ≃˘⟨ AA.subst₂ AA.absorb ⟩
                a * b + a * 0
              ∎

            Ps : ℕ.step-case P
            Ps {k} a[b+k]≃ab+ak =
              begin
                a * (b + step k)
              ≃˘⟨ AA.subst₂ AA.fnOpCommᴿ ⟩
                a * step (b + k)
              ≃⟨ *-stepᴿ ⟩
                a * (b + k) + a
              ≃⟨ AA.subst₂ a[b+k]≃ab+ak ⟩
                a * b + a * k + a
              ≃⟨ AA.assoc ⟩
                a * b + (a * k + a)
              ≃˘⟨ AA.subst₂ *-stepᴿ ⟩
                a * b + a * step k
              ∎

    *-distributive-+ᴿ : AA.Distributive AA.handᴿ (AA.tc₂ _*_) _+_
    *-distributive-+ᴿ = AA.distributiveᴿ-from-distributiveᴸ

    *-associative : AA.Associative _*_
    *-associative = record { assoc = *-assoc }
      where
        *-assoc : ∀ {a b c} → (a * b) * c ≃ a * (b * c)
        *-assoc {a} {b} {c} = Eq.sym (ℕ.ind P P0 Ps b)
          where
            P = λ x → a * (x * c) ≃ (a * x) * c
            P0 =
              begin
                a * (0 * c)
              ≃⟨ AA.subst₂ AA.absorb ⟩
                a * 0
              ≃⟨ AA.absorb ⟩
                0
              ≃˘⟨ AA.absorb ⟩
                0 * c
              ≃˘⟨ AA.subst₂ AA.absorb ⟩
                (a * 0) * c
              ∎

            Ps : ℕ.step-case P
            Ps {k} a[kc]≃[ak]c =
              begin
                a * (step k * c)
              ≃⟨ AA.subst₂ *-stepᴸ ⟩
                a * (k * c + c)
              ≃⟨ AA.distrib ⟩
                a * (k * c) + a * c
              ≃⟨ AA.subst₂ a[kc]≃[ak]c ⟩
                (a * k) * c + a * c
              ≃˘⟨ AA.distrib ⟩
                (a * k + a) * c
              ≃˘⟨ AA.subst₂ *-stepᴿ ⟩
                (a * step k) * c
              ∎

  *-preserves-<ᴿ : {a b c : ℕ} → a < b → S.Positive c → a * c < b * c
  *-preserves-<ᴿ {a} {b} {c} a<b pos[c] =
    let a+d≃b = ℕ.<-elim-diff a<b
        pos[d] = ℕ.<-diff-pos a<b
        ac+dc≃bc = Eq.trans (Eq.sym AA.distrib) (AA.subst₂ a+d≃b)
        pos[dc] = AA.pres pos[d] pos[c]
        ac≤bc = ℕ.≤-intro-diff ac+dc≃bc
        pos[d[ac≤bc]] = AA.subst₁ (Eq.sym (ℕ.intro-diff-id ac+dc≃bc)) pos[dc]
     in ℕ.<-intro-≤pd ac≤bc pos[d[ac≤bc]]

  *-preserves-<ᴸ : {a b c : ℕ} → b < c → S.Positive a → a * b < a * c
  *-preserves-<ᴸ {a} {b} {c} b<c pos[a] =
    AA.substᴸ AA.comm (AA.substᴿ AA.comm (*-preserves-<ᴿ b<c pos[a]))

  instance
    *-cancellativeᴸ : AA.Cancellative AA.handᴸ _*_ _≃_ _≃_ S.Positive
    *-cancellativeᴸ = AA.cancellative *-cancelᴸ
      where
        *-cancelᴸ :
          {a : ℕ} {{_ : S.Positive a}} {b c : ℕ} → a * b ≃ a * c → b ≃ c
        *-cancelᴸ {a} {b} {c} ab≃ac with
          AA.ExactlyOneOfThree.at-least-one (ℕ.order-trichotomy b c)
        ... | AA.1st b<c =
          let ab<ac = *-preserves-<ᴸ b<c it
              ab≄ac = ℕ.<-elim-≄ ab<ac
           in ab≃ac ↯ ab≄ac
        ... | AA.2nd b≃c =
          b≃c
        ... | AA.3rd b>c =
          let ac<ab = *-preserves-<ᴸ (Ord.>-flip b>c) it
              ac≄ab = ℕ.<-elim-≄ ac<ab
           in Eq.sym ab≃ac ↯ ac≄ab

    *-cancellativeᴿ : AA.Cancellative AA.handᴿ _*_ _≃_ _≃_ S.Positive
    *-cancellativeᴿ = AA.cancelᴿ-from-cancelᴸ-comm

    *-cancellative² : AA.Cancellative² _*_ _≃_ _≃_ S.Positive
    *-cancellative² = AA.cancellative²
