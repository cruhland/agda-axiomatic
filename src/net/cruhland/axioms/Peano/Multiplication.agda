module net.cruhland.axioms.Peano.Multiplication where

open import Relation.Nullary.Decidable using (False)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Ordering using (_<_)
open import net.cruhland.axioms.Operators as Op using (_+_; _*_)
open import net.cruhland.axioms.Peano.Addition using (Addition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
import net.cruhland.axioms.Peano.Literals as Literals
open import net.cruhland.axioms.Peano.Ordering using (Ordering)
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
open import net.cruhland.axioms.Sign as Sign using (Positive)
open import net.cruhland.models.Function using (it)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (_∧_; ∧-elimᴿ; ∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; contra)

record Multiplication
    (PB : PeanoBase)
    (PS : ℕSign PB)
    (PA : Addition PB PS)
    (PO : Ordering PB PS PA)
    : Set where
  private module ℕ+ = Addition PA
  open PeanoBase PB using (ℕ; ind; step; step-case; zero)
  private module Inspect = PeanoInspect PB
  open Inspect using (case; case-step; case-zero; pred-intro)
  private module ℕLit = Literals PB
  private module ℕOrd = Ordering PO
  private module ℕS = ℕSign PS

  field
    {{star}} : Op.Star ℕ
    {{*-substitutiveᴸ}} : AA.Substitutive₂ AA.handᴸ _*_ _≃_ _≃_
    {{*-absorptiveᴸ}} : AA.Absorptive AA.handᴸ _*_ 0
    *-stepᴸ : ∀ {n m} → step n * m ≃ n * m + m

  instance
    *-absorptiveᴿ : AA.Absorptive AA.handᴿ _*_ 0
    *-absorptiveᴿ = AA.absorptive *-zeroᴿ
      where
        *-zeroᴿ : ∀ {n} → n * 0 ≃ 0
        *-zeroᴿ {n} = ind P P0 Ps n
          where
            P = λ x → x * 0 ≃ 0
            P0 = AA.absorbᴸ

            Ps : step-case P
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

  *-stepᴿ : ∀ {n m} → n * step m ≃ n * m + n
  *-stepᴿ {n} {m} = ind P P0 Ps n
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

      Ps : step-case P
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
        *-comm {n} {m} = ind P P0 Ps n
          where
            P = λ x → x * m ≃ m * x
            P0 = Eq.trans AA.absorb (Eq.sym AA.absorb)

            Ps : step-case P
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
    zero-product = AA.zeroProduct 0 *-either-zero
      where
        *-either-zero : ∀ {n m} → n * m ≃ 0 → n ≃ 0 ∨ m ≃ 0
        *-either-zero {n} {m} n*m≃0 with case n
        ... | case-zero n≃0 = ∨-introᴸ n≃0
        ... | case-step (pred-intro p n≃sp) = ∨-introᴿ m≃0
          where
            p*m+m≃0 =
              begin
                p * m + m
              ≃˘⟨ *-stepᴸ ⟩
                step p * m
              ≃˘⟨ AA.subst₂ n≃sp ⟩
                n * m
              ≃⟨ n*m≃0 ⟩
                0
              ∎

            m≃0 = ∧-elimᴿ (ℕ+.+-both-zero p*m+m≃0)

    *-preserves-Positive : AA.Preserves Positive _*_
    *-preserves-Positive = AA.preserves *-pres-pos
      where
        *-pres-pos : {n m : ℕ} → Positive n → Positive m → Positive (n * m)
        *-pres-pos pos[n] pos[m] =
          let n≄0 = Sign.pos≄0 pos[n]
              m≄0 = Sign.pos≄0 pos[m]
           in ℕS.Pos-intro-≄0 (AA.nonzero-prod n≄0 m≄0)

    *-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _*_ _≃_ _≃_
    *-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm

    *-substitutive₂² : AA.Substitutive₂² _*_ _≃_ _≃_
    *-substitutive₂² = AA.substitutive₂²

    *-distributive-+ᴸ : AA.Distributive AA.handᴸ _*_ _+_
    *-distributive-+ᴸ = AA.distributive *-distrib-+ᴸ
      where
        *-distrib-+ᴸ : ∀ {a b c} → a * (b + c) ≃ a * b + a * c
        *-distrib-+ᴸ {a} {b} {c} = ind P P0 Ps c
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

            Ps : step-case P
            Ps {k} a[b+k]≃ab+ak =
              begin
                a * (b + step k)
              ≃˘⟨ AA.subst₂ AA.fnOpComm ⟩
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

    *-distributive-+ᴿ : AA.Distributive AA.handᴿ _*_ _+_
    *-distributive-+ᴿ = AA.distributiveᴿ-from-distributiveᴸ

    *-associative : AA.Associative _*_
    *-associative = record { assoc = *-assoc }
      where
        *-assoc : ∀ {a b c} → (a * b) * c ≃ a * (b * c)
        *-assoc {a} {b} {c} = Eq.sym (ind P P0 Ps b)
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

            Ps : step-case P
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

  *-preserves-<ᴿ : {a b c : ℕ} → a < b → Positive c → a * c < b * c
  *-preserves-<ᴿ {a} {b} {c} a<b pos[c] =
    let a+d≃b = ℕOrd.<-elim-diff a<b
        pos[d] = ℕOrd.<-diff-pos a<b
        ac+dc≃bc = Eq.trans (Eq.sym AA.distrib) (AA.subst₂ a+d≃b)
        pos[dc] = AA.pres pos[d] pos[c]
        ac≤bc = ℕOrd.≤-intro-diff ac+dc≃bc
        pos[d[ac≤bc]] = AA.subst₁ (Eq.sym (ℕOrd.intro-diff-id ac+dc≃bc)) pos[dc]
     in ℕOrd.<-intro-≤pd ac≤bc pos[d[ac≤bc]]

  *-preserves-<ᴸ : {a b c : ℕ} → b < c → Positive a → a * b < a * c
  *-preserves-<ᴸ {a} {b} {c} b<c pos[a] =
    AA.substᴸ AA.comm (AA.substᴿ AA.comm (*-preserves-<ᴿ b<c pos[a]))

  instance
    *-cancellativeᴸ : AA.Cancellative AA.handᴸ _*_ _≃_
    *-cancellativeᴸ = AA.cancellative λ a {{_ : C a}} {b c} → *-cancelᴸ
      where
        C = Positive

        *-cancelᴸ : {a b c : ℕ} {{_ : C a}} → a * b ≃ a * c → b ≃ c
        *-cancelᴸ {a} {b} {c} ab≃ac with
          AA.ExactlyOneOfThree.at-least-one (ℕOrd.order-trichotomy b c)
        ... | AA.1st b<c =
          let ab<ac = *-preserves-<ᴸ b<c it
              ab≄ac = ℕOrd.<-elim-≄ ab<ac
           in contra ab≃ac ab≄ac
        ... | AA.2nd b≃c =
          b≃c
        ... | AA.3rd b>c =
          let ac<ab = *-preserves-<ᴸ b>c it
              ac≄ab = ℕOrd.<-elim-≄ ac<ab
           in contra (Eq.sym ab≃ac) ac≄ab

    *-cancellativeᴿ : AA.Cancellative AA.handᴿ _*_ _≃_
    *-cancellativeᴿ = AA.cancelᴿ-from-cancelᴸ-comm

    *-cancellative² : AA.Cancellative² _*_ _≃_
    *-cancellative² = AA.cancellative²
