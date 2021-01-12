module net.cruhland.axioms.Peano.Addition where

import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
import net.cruhland.axioms.Operators as Op
open Op using (_+_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
import net.cruhland.axioms.Peano.Literals as PeanoLiterals
open import net.cruhland.models.Function using (const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (⊤; _∧_; _∨_; ∨-introᴸ; ∨-introᴿ; ¬_; contra; ¬[¬a∨¬b]→a∧b)

record Addition (PB : PeanoBase) : Set where
  open PeanoBase PB using (ℕ; ind; step; step-case; step≄zero; zero)
  open PeanoInspect PB using (case; case-zero; case-step; decEq; pred-intro)
  module ℕLit = PeanoLiterals PB

  field
    {{plus}} : Op.Plus ℕ
    {{+-substitutiveᴸ}} : AA.Substitutiveᴸ _+_
    {{+-identityᴸ}} : AA.Identityᴸ _+_ 0
    {{+-commutative-stepᴸ}} : AA.Commutativeᴸ step _+_

  instance
    +-identityᴿ : AA.Identityᴿ _+_ 0
    +-identityᴿ = record { identᴿ = +-zeroᴿ }
      where
        +-zeroᴿ : ∀ {n} → n + 0 ≃ n
        +-zeroᴿ {n} = ind P Pz Ps n
          where
            P = λ x → x + 0 ≃ x
            Pz = AA.identᴸ

            Ps : step-case P
            Ps {k} k+z≃k =
              begin
                step k + 0
              ≃⟨ AA.commᴸ ⟩
                step (k + 0)
              ≃⟨ AA.subst k+z≃k ⟩
                step k
              ∎

    +-commutative-stepᴿ : AA.Commutativeᴿ step _+_
    +-commutative-stepᴿ = record { commᴿ = +-stepᴿ }
      where
        +-stepᴿ : ∀ {n m} → n + step m ≃ step (n + m)
        +-stepᴿ {n} {m} = ind P Pz Ps n
          where
            P = λ x → x + step m ≃ step (x + m)

            Pz =
              begin
                0 + step m
              ≃⟨ AA.identᴸ ⟩
                step m
              ≃˘⟨ AA.subst AA.identᴸ ⟩
                step (0 + m)
              ∎

            Ps : step-case P
            Ps {k} k+sm≃s[k+m] =
              begin
                step k + step m
              ≃⟨ AA.commᴸ ⟩
                step (k + step m)
              ≃⟨ AA.subst k+sm≃s[k+m] ⟩
                step (step (k + m))
              ≃˘⟨ AA.subst AA.commᴸ ⟩
                step (step k + m)
              ∎

    +-commutative : AA.Commutative _+_
    +-commutative = record { comm = +-comm }
      where
        +-comm : ∀ {n m} → n + m ≃ m + n
        +-comm {n} {m} = ind P Pz Ps n
          where
            P = λ x → x + m ≃ m + x
            Pz =
              begin
                0 + m
              ≃⟨ AA.identᴸ ⟩
                m
              ≃˘⟨ AA.identᴿ ⟩
                m + 0
              ∎

            Ps : step-case P
            Ps {k} k+m≃m+k =
              begin
                step k + m
              ≃⟨ AA.commᴸ ⟩
                step (k + m)
              ≃⟨ AA.subst k+m≃m+k ⟩
                step (m + k)
              ≃˘⟨ AA.commᴿ ⟩
                m + step k
              ∎

    +-substitutiveᴿ : AA.Substitutiveᴿ _+_
    +-substitutiveᴿ = AA.substitutiveᴿ

    +-substitutive₂ : AA.Substitutive₂ _+_
    +-substitutive₂ = AA.substitutive₂

    +-associative : AA.Associative _+_
    +-associative = record { assoc = +-assoc }
      where
        +-assoc : ∀ {n m p} → (n + m) + p ≃ n + (m + p)
        +-assoc {n} {m} {p} = ind P Pz Ps n
          where
            P = λ x → (x + m) + p ≃ x + (m + p)

            Pz =
              begin
                (0 + m) + p
              ≃⟨ AA.subst AA.identᴸ ⟩
                m + p
              ≃˘⟨ AA.identᴸ ⟩
                0 + (m + p)
              ∎

            Ps : step-case P
            Ps {k} [k+m]+p≃k+[m+p] =
              begin
                (step k + m) + p
              ≃⟨ AA.subst AA.commᴸ ⟩
                step (k + m) + p
              ≃⟨ AA.commᴸ ⟩
                step ((k + m) + p)
              ≃⟨ AA.subst [k+m]+p≃k+[m+p] ⟩
                step (k + (m + p))
              ≃˘⟨ AA.commᴸ ⟩
                step k + (m + p)
              ∎

    +-cancellativeᴸ : AA.Cancellativeᴸ _+_ _≃_
    +-cancellativeᴸ = AA.cancellativeᴸ +-cancelᴸ
      where
        +-cancelᴸ : ∀ {n m p} → n + m ≃ n + p → m ≃ p
        +-cancelᴸ {n} {m} {p} = ind P Pz Ps n
          where
            P = λ x → x + m ≃ x + p → m ≃ p

            Pz : P 0
            Pz z+m≃z+p =
              begin
                m
              ≃˘⟨ AA.identᴸ ⟩
                0 + m
              ≃⟨ z+m≃z+p ⟩
                0 + p
              ≃⟨ AA.identᴸ ⟩
                p
              ∎

            Ps : step-case P
            Ps {k} k+m≃k+p→m≃p sk+m≃sk+p = k+m≃k+p→m≃p (AA.inject s[k+m]≃s[k+p])
              where
                s[k+m]≃s[k+p] =
                  begin
                    step (k + m)
                  ≃˘⟨ AA.commᴸ ⟩
                    step k + m
                  ≃⟨ sk+m≃sk+p ⟩
                    step k + p
                  ≃⟨ AA.commᴸ ⟩
                    step (k + p)
                  ∎

    +-cancellativeᴿ : AA.Cancellativeᴿ _+_ _≃_
    +-cancellativeᴿ = AA.cancellativeᴿ-from-cancellativeᴸ

  sn≃n+1 : ∀ {n} → step n ≃ n + 1
  sn≃n+1 {n} =
    begin
      step n
    ≃˘⟨ AA.subst AA.identᴿ ⟩
      step (n + 0)
    ≃˘⟨ AA.commᴿ ⟩
      n + step 0
    ≃⟨⟩
      n + 1
    ∎

  n≄sn : ∀ {n} → n ≄ step n
  n≄sn {n} n≃sn = contra (AA.cancelᴸ n+1≃n+0) step≄zero
    where
      n+1≃n+0 =
        begin
          n + 1
        ≃˘⟨ sn≃n+1 ⟩
          step n
        ≃˘⟨ n≃sn ⟩
          n
        ≃˘⟨ AA.identᴿ ⟩
          n + 0
        ∎

  Positive : ℕ → Set
  Positive n = n ≄ 0

  Positive-subst : ∀ {n₁ n₂} → n₁ ≃ n₂ → Positive n₁ → Positive n₂
  Positive-subst n₁≃n₂ n₁≄z n₂≃z = n₁≄z (trans n₁≃n₂ n₂≃z)

  +-positive : ∀ {a b} → Positive a → Positive (a + b)
  +-positive {a} {b} pos-a = ind P Pz Ps b
    where
      P = λ x → Positive (a + x)

      Pz : P 0
      Pz = Positive-subst (sym AA.identᴿ) pos-a

      Ps : step-case P
      Ps {k} _ = λ a+sk≃z → step≄zero (trans (sym AA.commᴿ) a+sk≃z)

  +-both-zero : {a b : ℕ} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
  +-both-zero {a} {b} a+b≃z =
    ¬[¬a∨¬b]→a∧b (a ≃? 0) (b ≃? 0) neither-positive
      where
        neither-positive : ¬ (a ≄ 0 ∨ b ≄ 0)
        neither-positive (∨-introᴸ a≄z) = +-positive a≄z a+b≃z
        neither-positive (∨-introᴿ b≄z) = +-positive b≄z (trans AA.comm a+b≃z)
