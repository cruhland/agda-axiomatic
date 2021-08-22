import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_)
open Eq.≃-Reasoning
open import net.cruhland.axioms.Operators as Op using (_+_)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
import net.cruhland.axioms.Peano.Literals as PeanoLiterals
open import net.cruhland.axioms.Peano.Sign using () renaming (Sign to ℕSign)
import net.cruhland.axioms.Sign as S
open import net.cruhland.models.Function using (_∘_; const)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic
  using (⊤; _∧_; _∨_; ∨-introᴸ; ∨-introᴿ
        ; _↯_; ¬_; ¬-intro; ¬[¬a∨¬b]→a∧b; contrapositive)

module net.cruhland.axioms.Peano.Addition where

private module Predefs (PB : PeanoBase) (PS : ℕSign PB) where
  open PeanoBase PB public
  open PeanoInspect PB public
  open PeanoLiterals PB public
  open ℕSign PS public

record Addition (PB : PeanoBase) (PS : ℕSign PB) : Set where
  private module ℕ = Predefs PB PS
  open ℕ using (ℕ; ind; step; step-case; step≄zero)

  field
    {{plus}} : Op.Plus ℕ
    {{+-substitutiveᴸ}} : AA.Substitutive₂ AA.handᴸ _+_ _≃_ _≃_
    {{+-identityᴸ}} : AA.Identity AA.handᴸ _+_ 0
    {{+-fnOpCommutative-stepᴸ}} :
      AA.FnOpCommutative AA.handᴸ step step (AA.tc₂ _+_)

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
              ≃˘⟨ AA.fnOpCommᴸ ⟩
                step (k + 0)
              ≃⟨ AA.subst₁ k+z≃k ⟩
                step k
              ∎

    +-fnOpCommutative-stepᴿ : AA.FnOpCommutative AA.handᴿ step step (AA.tc₂ _+_)
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
              ≃˘⟨ AA.subst₁ AA.fnOpCommᴸ ⟩
                step (step (k + m))
              ≃⟨ AA.subst₁ s[k+m]≃k+sm ⟩
                step (k + step m)
              ≃⟨ AA.fnOpCommᴸ ⟩
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
              ≃˘⟨ AA.fnOpCommᴸ ⟩
                step (k + m)
              ≃⟨ AA.subst₁ k+m≃m+k ⟩
                step (m + k)
              ≃⟨ AA.fnOpCommᴿ ⟩
                m + step k
              ∎

    +-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≃_ _≃_
    +-substitutiveᴿ = AA.substᴿ-from-substᴸ-comm

    +-substitutive : AA.Substitutive² _+_ _≃_ _≃_
    +-substitutive = AA.substitutive²

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
              ≃˘⟨ AA.subst₂ AA.fnOpCommᴸ ⟩
                step (k + m) + p
              ≃˘⟨ AA.fnOpCommᴸ ⟩
                step ((k + m) + p)
              ≃⟨ AA.subst₁ [k+m]+p≃k+[m+p] ⟩
                step (k + (m + p))
              ≃⟨ AA.fnOpCommᴸ ⟩
                step k + (m + p)
              ∎

    +-cancellativeᴸ : AA.Cancellative AA.handᴸ _+_ _≃_ _≃_ (const ⊤)
    +-cancellativeᴸ = AA.cancellative +-cancelᴸ
      where
        +-cancelᴸ : ∀ {n m p} {{_ : ⊤}} → n + m ≃ n + p → m ≃ p
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
                  ≃⟨ AA.fnOpCommᴸ ⟩
                    step k + m
                  ≃⟨ sk+m≃sk+p ⟩
                    step k + p
                  ≃˘⟨ AA.fnOpCommᴸ ⟩
                    step (k + p)
                  ∎

    +-cancellativeᴿ : AA.Cancellative AA.handᴿ _+_ _≃_ _≃_ (const ⊤)
    +-cancellativeᴿ = AA.cancelᴿ-from-cancelᴸ-comm

    +-cancellative² : AA.Cancellative² _+_ _≃_ _≃_ (const ⊤)
    +-cancellative² = AA.cancellative²

    +-substitutive-≄ᴸ : AA.Substitutive₂ AA.handᴸ _+_ _≄_ _≄_
    +-substitutive-≄ᴸ = AA.substitutive₂ +-subst-≄ᴸ
      where
        +-subst-≄ᴸ : {n₁ n₂ m : ℕ} → n₁ ≄ n₂ → n₁ + m ≄ n₂ + m
        +-subst-≄ᴸ n₁≄n₂ = contrapositive AA.cancel n₁≄n₂

    +-substitutive-≄ᴿ : AA.Substitutive₂ AA.handᴿ _+_ _≄_ _≄_
    +-substitutive-≄ᴿ = AA.substᴿ-from-substᴸ-comm₂

    +-substitutive-≄ : AA.Substitutive² _+_ _≄_ _≄_
    +-substitutive-≄ = AA.substitutive²

  sn≃n+1 : ∀ {n} → step n ≃ n + 1
  sn≃n+1 {n} =
    begin
      step n
    ≃˘⟨ AA.subst₁ AA.ident ⟩
      step (n + 0)
    ≃⟨ AA.fnOpCommᴿ ⟩
      n + step 0
    ≃⟨⟩
      n + 1
    ∎

  n≄sn : ∀ {n} → n ≄ step n
  n≄sn {n} = Eq.≄-intro λ n≃sn →
    let n+1≃n+0 =
          begin
            n + 1
          ≃˘⟨ sn≃n+1 ⟩
            step n
          ≃˘⟨ n≃sn ⟩
            n
          ≃˘⟨ AA.ident ⟩
            n + 0
          ∎
        1≃0 = AA.cancel n+1≃n+0
        1≄0 = step≄zero
     in 1≃0 ↯ 1≄0

  +-positive : {a b : ℕ} → S.Positive a → S.Positive (a + b)
  +-positive {a} {b} pos-a = ind P P0 Ps b
    where
      P = λ x → S.Positive (a + x)

      P0 : P 0
      P0 = AA.subst₁ (Eq.sym AA.ident) pos-a

      Ps : step-case P
      Ps {k} _ =
        let s[a+k]≄0 = step≄zero
            a+sk≄0 = AA.substᴸ AA.fnOpCommᴿ s[a+k]≄0
         in ℕ.Pos-intro-≄0 a+sk≄0

  instance
    +-preserves-Positive : AA.Preserves S.Positive _+_
    +-preserves-Positive = AA.preserves +-pres-pos
      where
        +-pres-pos :
          {n m : ℕ} → S.Positive n → S.Positive m → S.Positive (n + m)
        +-pres-pos pos[n] pos[m] = +-positive pos[n]

    positivityCommon : S.PositivityCommon ℕ
    positivityCommon = record {}

  +-nonzero : {x y : ℕ} → x ≄ 0 → x + y ≄ 0
  +-nonzero = S.pos≄0 ∘ +-positive ∘ ℕ.Pos-intro-≄0

  +-both-zero : {a b : ℕ} → a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0
  +-both-zero {a} {b} a+b≃0 =
    ¬[¬a∨¬b]→a∧b (a ≃? 0) (b ≃? 0) neither-positive
      where
        neither-positive : ¬ (a ≄ 0 ∨ b ≄ 0)
        neither-positive = ¬-intro λ
          { (∨-introᴸ a≄0) →
              let a+b≄0 = +-nonzero a≄0
               in a+b≃0 ↯ a+b≄0
          ; (∨-introᴿ b≄0) →
              let b+a≃0 = Eq.trans AA.comm a+b≃0
                  b+a≄0 = +-nonzero b≄0
               in b+a≃0 ↯ b+a≄0
          }
