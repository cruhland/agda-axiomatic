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
open import net.cruhland.axioms.Peano.Sign using (Sign)
open import net.cruhland.axioms.Sign using (nonzero; Positive)
open import net.cruhland.models.Function using (_∘_; const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using
  (⊤; _∧_; _∨_; ∨-introᴸ; ∨-introᴿ; ¬_; contra; ¬[¬a∨¬b]→a∧b)

record Addition (PB : PeanoBase) (PS : Sign PB) : Set where
  open PeanoBase PB using (ℕ; ind; step; step-case; step≄zero; zero)
  open PeanoInspect PB using (case; case-zero; case-step; decEq; pred-intro)
  private module ℕLit = PeanoLiterals PB
  open Sign PS using (mkPositive)

  field
    {{plus}} : Op.Plus ℕ
    {{+-substitutiveᴸ}} : AA.Substitutive₂ AA.handᴸ _+_ _≃_ _≃_
    {{+-identityᴸ}} : AA.Identity AA.handᴸ _+_ 0
    {{+-fnOpCommutative-stepᴸ}} : AA.FnOpCommutative AA.handᴸ step _+_

  instance
    +-identityᴿ : AA.Identity AA.handᴿ _+_ 0
    +-identityᴿ = AA.identity +-zeroᴿ
      where
        +-zeroᴿ : ∀ {n} → n + 0 ≃ n
        +-zeroᴿ {n} = ind P P0 Ps n
          where
            P = λ x → x + 0 ≃ x
            P0 = AA.identᴸ

            Ps : step-case P
            Ps {k} k+z≃k =
              begin
                step k + 0
              ≃˘⟨ AA.fnOpComm ⟩
                step (k + 0)
              ≃⟨ AA.subst₁ k+z≃k ⟩
                step k
              ∎

    +-fnOpCommutative-stepᴿ : AA.FnOpCommutative AA.handᴿ step _+_
    +-fnOpCommutative-stepᴿ = AA.fnOpCommutative +-stepᴿ
      where
        +-stepᴿ : ∀ {n m} → step (n + m) ≃ n + step m
        +-stepᴿ {n} {m} = ind P Pz Ps n
          where
            P = λ x → step (x + m) ≃ x + step m

            Pz =
              begin
                step (0 + m)
              ≃⟨ AA.subst₁ AA.ident ⟩
                step m
              ≃˘⟨ AA.ident ⟩
                0 + step m
              ∎

            Ps : step-case P
            Ps {k} s[k+m]≃k+sm =
              begin
                step (step k + m)
              ≃˘⟨ AA.subst₁ AA.fnOpComm ⟩
                step (step (k + m))
              ≃⟨ AA.subst₁ s[k+m]≃k+sm ⟩
                step (k + step m)
              ≃⟨ AA.fnOpComm ⟩
                step k + step m
              ∎

    +-commutative : AA.Commutative _+_
    +-commutative = AA.commutative +-comm
      where
        +-comm : ∀ {n m} → n + m ≃ m + n
        +-comm {n} {m} = ind P Pz Ps n
          where
            P = λ x → x + m ≃ m + x
            Pz =
              begin
                0 + m
              ≃⟨ AA.ident ⟩
                m
              ≃˘⟨ AA.ident ⟩
                m + 0
              ∎

            Ps : step-case P
            Ps {k} k+m≃m+k =
              begin
                step k + m
              ≃˘⟨ AA.fnOpComm ⟩
                step (k + m)
              ≃⟨ AA.subst₁ k+m≃m+k ⟩
                step (m + k)
              ≃⟨ AA.fnOpComm ⟩
                m + step k
              ∎

    +-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≃_ _≃_
    +-substitutiveᴿ = AA.substitutiveᴿ-from-substitutiveᴸ
      where instance +-swappable = AA.swappable-from-commutative

    +-substitutive₂² : AA.Substitutive₂² _+_ _≃_ _≃_
    +-substitutive₂² = AA.substitutive₂²

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
              ≃⟨ AA.subst₂ AA.ident ⟩
                m + p
              ≃˘⟨ AA.ident ⟩
                0 + (m + p)
              ∎

            Ps : step-case P
            Ps {k} [k+m]+p≃k+[m+p] =
              begin
                (step k + m) + p
              ≃˘⟨ AA.subst₂ AA.fnOpComm ⟩
                step (k + m) + p
              ≃˘⟨ AA.fnOpComm ⟩
                step ((k + m) + p)
              ≃⟨ AA.subst₁ [k+m]+p≃k+[m+p] ⟩
                step (k + (m + p))
              ≃⟨ AA.fnOpComm ⟩
                step k + (m + p)
              ∎

    +-cancellativeᴸ : AA.Cancellative AA.handᴸ _+_ _≃_
    +-cancellativeᴸ = AA.cancellative λ {n m p} → +-cancelᴸ
      where
        +-cancelᴸ : ∀ {n m p} → n + m ≃ n + p → m ≃ p
        +-cancelᴸ {n} {m} {p} = ind P Pz Ps n
          where
            P = λ x → x + m ≃ x + p → m ≃ p

            Pz : P 0
            Pz z+m≃z+p =
              begin
                m
              ≃˘⟨ AA.ident ⟩
                0 + m
              ≃⟨ z+m≃z+p ⟩
                0 + p
              ≃⟨ AA.ident ⟩
                p
              ∎

            Ps : step-case P
            Ps {k} k+m≃k+p→m≃p sk+m≃sk+p = k+m≃k+p→m≃p (AA.inject s[k+m]≃s[k+p])
              where
                s[k+m]≃s[k+p] =
                  begin
                    step (k + m)
                  ≃⟨ AA.fnOpComm ⟩
                    step k + m
                  ≃⟨ sk+m≃sk+p ⟩
                    step k + p
                  ≃˘⟨ AA.fnOpComm ⟩
                    step (k + p)
                  ∎

    +-cancellativeᴿ : AA.Cancellative AA.handᴿ _+_ _≃_
    +-cancellativeᴿ = AA.cancellativeᴿ-from-cancellativeᴸ

  sn≃n+1 : ∀ {n} → step n ≃ n + 1
  sn≃n+1 {n} =
    begin
      step n
    ≃˘⟨ AA.subst₁ AA.ident ⟩
      step (n + 0)
    ≃⟨ AA.fnOpComm ⟩
      n + step 0
    ≃⟨⟩
      n + 1
    ∎

  n≄sn : ∀ {n} → n ≄ step n
  n≄sn {n} n≃sn = contra (AA.cancel n+1≃n+0) step≄zero
    where
      n+1≃n+0 =
        begin
          n + 1
        ≃˘⟨ sn≃n+1 ⟩
          step n
        ≃˘⟨ n≃sn ⟩
          n
        ≃˘⟨ AA.ident ⟩
          n + 0
        ∎

  +-positive : {a b : ℕ} → Positive a → Positive (a + b)
  +-positive {a} {b} pos-a = ind P P0 Ps b
    where
      P = λ x → Positive (a + x)

      P0 : P 0
      P0 = AA.subst₁ (sym AA.ident) pos-a

      Ps : step-case P
      Ps {k} _ = mkPositive λ a+sk≃0 → step≄zero (trans AA.fnOpComm a+sk≃0)

  +-nonzero : {x y : ℕ} → x ≄ 0 → x + y ≄ 0
  +-nonzero = nonzero ∘ +-positive ∘ mkPositive

  +-both-zero : {a b : ℕ} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
  +-both-zero {a} {b} a+b≃0 =
    ¬[¬a∨¬b]→a∧b (a ≃? 0) (b ≃? 0) neither-positive
      where
        neither-positive : ¬ (a ≄ 0 ∨ b ≄ 0)
        neither-positive (∨-introᴸ a≄0) = +-nonzero a≄0 a+b≃0
        neither-positive (∨-introᴿ b≄0) = +-nonzero b≄0 (trans AA.comm a+b≃0)
