module net.cruhland.axioms.Peano.Multiplication where

open import Relation.Nullary.Decidable using (False)
open import net.cruhland.axioms.Cast using (_as_)
open import net.cruhland.axioms.DecEq using (_≃?_; ≄-derive)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.AbstractAlgebra as AA
import net.cruhland.axioms.Operators as Op
open Op using (_+_; _*_)
open import net.cruhland.axioms.Peano.Addition
  using () renaming (Addition to PeanoAddition)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
import net.cruhland.axioms.Peano.Ordering as PeanoOrdering
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (_∧_; ∧-elimᴿ; ∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; contra)

record Multiplication (PB : PeanoBase) (PA : PeanoAddition PB) : Set where
  private module Add = PeanoAddition PA
  open Add using (+-both-zero; Positive)
  open PeanoBase PB using (ℕ; ind; step; step-case; zero)
  private module Inspect = PeanoInspect PB
  open Inspect using (case; case-step; case-zero; pred-intro)
  private module ℕ≤ = PeanoOrdering PB PA
  open ℕ≤ using (_<_; _<⁺_; ≤-intro; <-intro; <⁺-intro)

  field
    {{star}} : Op.Star ℕ
    {{*-substitutiveᴸ}} : AA.Substitutiveᴸ _*_
    {{*-absorptiveᴸ}} : AA.Absorptiveᴸ _*_ zero
    *-stepᴸ : ∀ {n m} → step n * m ≃ n * m + m

  instance
    *-absorptiveᴿ : AA.Absorptiveᴿ _*_ zero
    *-absorptiveᴿ = record { absorbᴿ = *-zeroᴿ }
      where
        *-zeroᴿ : ∀ {n} → n * zero ≃ zero
        *-zeroᴿ {n} = ind P Pz Ps n
          where
            P = λ x → x * zero ≃ zero
            Pz = AA.absorbᴸ

            Ps : step-case P
            Ps {k} Pk =
              begin
                step k * zero
              ≃⟨ *-stepᴸ ⟩
                k * zero + zero
              ≃⟨ AA.identᴿ ⟩
                k * zero
              ≃⟨ Pk ⟩
                zero
              ∎

  *-stepᴿ : ∀ {n m} → n * step m ≃ n * m + n
  *-stepᴿ {n} {m} = ind P Pz Ps n
    where
      P = λ x → x * step m ≃ x * m + x

      Pz =
        begin
          zero * step m
        ≃⟨ AA.absorbᴸ ⟩
          zero
        ≃˘⟨ AA.absorbᴸ ⟩
          zero * m
        ≃˘⟨ AA.identᴿ ⟩
          zero * m + zero
        ∎

      Ps : step-case P
      Ps {k} Pk =
        begin
          step k * step m
        ≃⟨ *-stepᴸ ⟩
          k * step m + step m
        ≃⟨ AA.subst Pk ⟩
          k * m + k + step m
        ≃⟨ AA.substᴿ-with-assoc (trans AA.comm AA.comm-swap) ⟩
          k * m + m + step k
        ≃˘⟨ AA.subst *-stepᴸ ⟩
          step k * m + step k
        ∎

  instance
    *-commutative : AA.Commutative _*_
    *-commutative = record { comm = *-comm }
      where
        *-comm : ∀ {n m} → n * m ≃ m * n
        *-comm {n} {m} = ind P Pz Ps n
          where
            P = λ x → x * m ≃ m * x
            Pz = trans AA.absorbᴸ (sym AA.absorbᴿ)

            Ps : step-case P
            Ps {k} Pk =
              begin
                step k * m
              ≃⟨ *-stepᴸ ⟩
                k * m + m
              ≃⟨ AA.subst Pk ⟩
                m * k + m
              ≃˘⟨ *-stepᴿ ⟩
                m * step k
              ∎

    *-identityᴸ : AA.Identityᴸ _*_ (step zero)
    *-identityᴸ = record { identᴸ = *-oneᴸ }
      where
        *-oneᴸ : ∀ {n} → step zero * n ≃ n
        *-oneᴸ {n} =
          begin
            step zero * n
          ≃⟨ *-stepᴸ ⟩
            zero * n + n
          ≃⟨ AA.subst AA.absorbᴸ ⟩
            zero + n
          ≃⟨ AA.identᴸ ⟩
            n
          ∎

    *-identityᴿ : AA.Identityᴿ _*_ (step zero)
    *-identityᴿ = AA.identityᴿ

    zero-product : AA.ZeroProduct _*_ zero
    zero-product = record { zero-prod = *-either-zero }
      where
        *-either-zero : ∀ {n m} → n * m ≃ zero → n ≃ zero ∨ m ≃ zero
        *-either-zero {n} {m} n*m≃z with case n
        ... | case-zero n≃z = ∨-introᴸ n≃z
        ... | case-step (pred-intro p n≃sp) = ∨-introᴿ m≃z
          where
            p*m+m≃z =
              begin
                p * m + m
              ≃˘⟨ *-stepᴸ ⟩
                step p * m
              ≃˘⟨ AA.subst n≃sp ⟩
                n * m
              ≃⟨ n*m≃z ⟩
                zero
              ∎

            m≃z = ∧-elimᴿ (+-both-zero p*m+m≃z)

    *-substitutiveᴿ : AA.Substitutiveᴿ _*_
    *-substitutiveᴿ = AA.substitutiveᴿ

    *-substitutive₂ : AA.Substitutive₂ _*_
    *-substitutive₂ = AA.substitutive₂

    *-distributive-+ᴸ : AA.Distributiveᴸ _*_ _+_
    *-distributive-+ᴸ = record { distribᴸ = *-distrib-+ᴸ }
      where
        *-distrib-+ᴸ : ∀ {a b c} → a * (b + c) ≃ a * b + a * c
        *-distrib-+ᴸ {a} {b} {c} = ind P Pz Ps c
          where
            P = λ x → a * (b + x) ≃ a * b + a * x
            Pz =
              begin
                a * (b + zero)
              ≃⟨ AA.subst AA.identᴿ ⟩
                a * b
              ≃˘⟨ AA.identᴿ ⟩
                a * b + zero
              ≃˘⟨ AA.subst AA.absorbᴿ ⟩
                a * b + a * zero
              ∎

            Ps : step-case P
            Ps {k} a[b+k]≃ab+ak =
              begin
                a * (b + step k)
              ≃⟨ AA.subst AA.commᴿ ⟩
                a * step (b + k)
              ≃⟨ *-stepᴿ ⟩
                a * (b + k) + a
              ≃⟨ AA.subst a[b+k]≃ab+ak ⟩
                a * b + a * k + a
              ≃⟨ AA.assoc ⟩
                a * b + (a * k + a)
              ≃˘⟨ AA.subst *-stepᴿ ⟩
                a * b + a * step k
              ∎

    *-distributive-+ᴿ : AA.Distributiveᴿ _*_ _+_
    *-distributive-+ᴿ = AA.distributiveᴿ

    *-associative : AA.Associative _*_
    *-associative = record { assoc = *-assoc }
      where
        *-assoc : ∀ {a b c} → (a * b) * c ≃ a * (b * c)
        *-assoc {a} {b} {c} = sym (ind P Pz Ps b)
          where
            P = λ x → a * (x * c) ≃ (a * x) * c
            Pz =
              begin
                a * (zero * c)
              ≃⟨ AA.subst AA.absorbᴸ ⟩
                a * zero
              ≃⟨ AA.absorbᴿ ⟩
                zero
              ≃˘⟨ AA.absorbᴸ ⟩
                zero * c
              ≃˘⟨ AA.subst AA.absorbᴿ ⟩
                (a * zero) * c
              ∎

            Ps : step-case P
            Ps {k} a[kc]≃[ak]c =
              begin
                a * (step k * c)
              ≃⟨ AA.subst *-stepᴸ ⟩
                a * (k * c + c)
              ≃⟨ AA.distribᴸ ⟩
                a * (k * c) + a * c
              ≃⟨ AA.subst a[kc]≃[ak]c ⟩
                (a * k) * c + a * c
              ≃˘⟨ AA.distribᴿ ⟩
                (a * k + a) * c
              ≃˘⟨ AA.subst *-stepᴿ ⟩
                (a * step k) * c
              ∎

  *-preserves-<ᴿ : ∀ {a b c} → a < b → c ≄ 0 → a * c < b * c
  *-preserves-<ᴿ {a} {b} {c} a<b c≄0 =
    let <⁺-intro a≤b@(≤-intro d a+d≃b) d≄0 = a<b as a <⁺ b
        ac+dc≃bc = trans (sym AA.distribᴿ) (AA.subst a+d≃b)
        dc≄0 = AA.nonzero-prod d≄0 c≄0
     in <⁺-intro (≤-intro (d * c) ac+dc≃bc) dc≄0 as a * c < b * c

  *-preserves-<ᴸ : ∀ {a b c} → b < c → a ≄ zero → a * b < a * c
  *-preserves-<ᴸ {a} {b} {c} b<c a≄z =
    AA.subst {f = _< a * c} AA.comm (AA.subst AA.comm (*-preserves-<ᴿ b<c a≄z))

  instance
    *-cancellativeᴸ : AA.Cancellativeᴸ _*_
    *-cancellativeᴸ =
        record { Constraint = λ a → False (a ≃? zero) ; cancelᴸ = *-cancelᴸ }
      where
        *-cancelᴸ : ∀ {a b c} {{_ : False (a ≃? zero)}} → a * b ≃ a * c → b ≃ c
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

    *-cancellativeᴿ : AA.Cancellativeᴿ _≃_ _*_
    *-cancellativeᴿ = AA.cancellativeᴿ
