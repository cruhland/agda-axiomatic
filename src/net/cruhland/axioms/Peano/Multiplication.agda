module net.cruhland.axioms.Peano.Multiplication where

open import Relation.Nullary.Decidable using (False)
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Operators as Op
open Op using (_+_; _*_)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
import net.cruhland.axioms.Peano.Literals as Literals
import net.cruhland.axioms.Peano.Ordering as PeanoOrdering
open import net.cruhland.axioms.Peano.Sign using (Sign)
import net.cruhland.models.Function
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (_∧_; ∧-elimᴿ; ∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; contra)

record Multiplication
    (PB : PeanoBase) (PS : Sign PB) (PA : PeanoAddition PB PS) : Set where
  private module ℕ+ = PeanoAddition PA
  open PeanoBase PB using (ℕ; ind; step; step-case; zero)
  private module Inspect = PeanoInspect PB
  open Inspect using (case; case-step; case-zero; pred-intro)
  private module ℕLit = Literals PB
  private module ℕ≤ = PeanoOrdering PB PS PA
  open ℕ≤ using (_<_; _<⁺_; ≤-intro; <-intro; <⁺-intro)

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
        ≃⟨ AA.substᴿ-with-assoc (trans AA.comm AA.fnOpCommSwap) ⟩
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
            P0 = trans AA.absorb (sym AA.absorb)

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

    *-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _*_ _≃_ _≃_
    *-substitutiveᴿ = AA.substitutiveᴿ-from-substitutiveᴸ
      where instance *-swappable = AA.swappable-from-commutative

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
        *-assoc {a} {b} {c} = sym (ind P P0 Ps b)
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

  *-preserves-<ᴿ : ∀ {a b c} → a < b → c ≄ 0 → a * c < b * c
  *-preserves-<ᴿ {a} {b} {c} a<b c≄0 =
    let <⁺-intro a≤b@(≤-intro d a+d≃b) d≄0 = a<b as a <⁺ b
        ac+dc≃bc = trans (sym AA.distrib) (AA.subst₂ a+d≃b)
        dc≄0 = AA.nonzero-prod d≄0 c≄0
     in <⁺-intro (≤-intro (d * c) ac+dc≃bc) dc≄0 as a * c < b * c

  *-preserves-<ᴸ : ∀ {a b c} → b < c → a ≄ 0 → a * b < a * c
  *-preserves-<ᴸ {a} {b} {c} b<c a≄0 =
    AA.subst₁ {f = _< a * c} AA.comm (AA.subst₁ AA.comm (*-preserves-<ᴿ b<c a≄0))

  instance
    *-cancellativeᴸ : AA.Cancellative AA.handᴸ _*_ _≃_
    *-cancellativeᴸ = AA.cancellative λ a {{_ : C a}} {b c} → *-cancelᴸ
      where
        C = λ a → False (a ≃? 0)

        *-cancelᴸ : ∀ {a b c} {{_ : C a}} → a * b ≃ a * c → b ≃ c
        *-cancelᴸ ab≃ac with
          AA.ExactlyOneOfThree.at-least-one ℕ≤.order-trichotomy
        ... | AA.1st b<c =
          let <-intro _ ab≄ac = *-preserves-<ᴸ b<c ≄-derive
           in contra ab≃ac ab≄ac
        ... | AA.2nd b≃c =
          b≃c
        ... | AA.3rd b>c =
          let <-intro _ ac≄ab = *-preserves-<ᴸ b>c ≄-derive
           in contra (sym ab≃ac) ac≄ab

    *-cancellativeᴿ : AA.Cancellative AA.handᴿ _*_ _≃_
    *-cancellativeᴿ = AA.cancellativeᴿ-from-cancellativeᴸ
