module net.cruhland.axioms.Peano.Multiplication where

open import Relation.Nullary.Decidable using (False)
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
open import net.cruhland.models.Logic using
  (_∧_; ∧-elimᴿ; ∧-intro; _∨_; ∨-introᴸ; ∨-introᴿ; contra)

record Multiplication (PB : PeanoBase) (PA : PeanoAddition PB) : Set where
  private module Add = PeanoAddition PA
  open Add using (+-both-zero; Positive; +-stepᴸ⃗ᴿ; with-+-assoc)
  open PeanoBase PB using (ℕ; ind; step; step-case; zero)
  private module Inspect = PeanoInspect PB
  open Inspect using (case; case-step; case-zero; pred-intro)
  open PeanoOrdering PB PA using
    (_<_; <⁺→<; <→<⁺; <-intro; <⁺-intro; <-substᴸ; <-substᴿ; order-trichotomy)

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
        ≃⟨ AA.substᴸ Pk ⟩
          k * m + k + step m
        ≃⟨ with-+-assoc (trans AA.comm +-stepᴸ⃗ᴿ) ⟩
          k * m + m + step k
        ≃˘⟨ AA.substᴸ *-stepᴸ ⟩
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
              ≃⟨ AA.substᴸ Pk ⟩
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
          ≃⟨ AA.substᴸ AA.absorbᴸ ⟩
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
              ≃˘⟨ AA.substᴸ n≃sp ⟩
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
              ≃⟨ AA.substᴿ AA.identᴿ ⟩
                a * b
              ≃˘⟨ AA.identᴿ ⟩
                a * b + zero
              ≃˘⟨ AA.substᴿ AA.absorbᴿ ⟩
                a * b + a * zero
              ∎

            Ps : step-case P
            Ps {k} a[b+k]≃ab+ak =
              begin
                a * (b + step k)
              ≃⟨ AA.substᴿ AA.commᴿ ⟩
                a * step (b + k)
              ≃⟨ *-stepᴿ ⟩
                a * (b + k) + a
              ≃⟨ AA.substᴸ a[b+k]≃ab+ak ⟩
                a * b + a * k + a
              ≃⟨ AA.assoc ⟩
                a * b + (a * k + a)
              ≃˘⟨ AA.substᴿ *-stepᴿ ⟩
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
              ≃⟨ AA.substᴿ AA.absorbᴸ ⟩
                a * zero
              ≃⟨ AA.absorbᴿ ⟩
                zero
              ≃˘⟨ AA.absorbᴸ ⟩
                zero * c
              ≃˘⟨ AA.substᴸ AA.absorbᴿ ⟩
                (a * zero) * c
              ∎

            Ps : step-case P
            Ps {k} a[kc]≃[ak]c =
              begin
                a * (step k * c)
              ≃⟨ AA.substᴿ *-stepᴸ ⟩
                a * (k * c + c)
              ≃⟨ AA.distribᴸ ⟩
                a * (k * c) + a * c
              ≃⟨ AA.substᴸ a[kc]≃[ak]c ⟩
                (a * k) * c + a * c
              ≃˘⟨ AA.distribᴿ ⟩
                (a * k + a) * c
              ≃˘⟨ AA.substᴸ *-stepᴿ ⟩
                (a * step k) * c
              ∎

  *-preserves-<ᴿ : ∀ {a b c} → a < b → c ≄ zero → a * c < b * c
  *-preserves-<ᴿ {a} {b} {c} a<b c≄z with <→<⁺ a<b
  ... | <⁺-intro d d≄z a+d≃b = <⁺→< (<⁺-intro (d * c) dc≄z ac+dc≃bc)
    where
      dc≄z = AA.nonzero-prod d≄z c≄z
      ac+dc≃bc = trans (sym AA.distribᴿ) (AA.substᴸ a+d≃b)

  *-preserves-<ᴸ : ∀ {a b c} → b < c → a ≄ zero → a * b < a * c
  *-preserves-<ᴸ b<c a≄z =
    <-substᴸ AA.comm (<-substᴿ AA.comm (*-preserves-<ᴿ b<c a≄z))

  instance
    *-cancellativeᴸ : AA.Cancellativeᴸ _*_
    *-cancellativeᴸ =
        record { Constraint = λ a → False (a ≃? zero) ; cancelᴸ = *-cancelᴸ }
      where
        *-cancelᴸ : ∀ {a b c} {{_ : False (a ≃? zero)}} → a * b ≃ a * c → b ≃ c
        *-cancelᴸ ab≃ac with AA.ExactlyOneOfThree.at-least-one order-trichotomy
        ... | AA.1st b<c =
          let <-intro _ ab≄ac = *-preserves-<ᴸ b<c ≄-derive
           in contra ab≃ac ab≄ac
        ... | AA.2nd b≃c =
          b≃c
        ... | AA.3rd b>c =
          let <-intro _ ac≄ab = *-preserves-<ᴸ b>c ≄-derive
           in contra (sym ab≃ac) ac≄ab

    *-cancellativeᴿ : AA.Cancellativeᴿ _*_
    *-cancellativeᴿ = AA.cancellativeᴿ
