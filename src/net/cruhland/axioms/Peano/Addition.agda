module net.cruhland.axioms.Peano.Addition where

open import Function using (const)
import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq using
  (_≃_; _≄_; sym; trans; module ≃-Reasoning)
open ≃-Reasoning
open import net.cruhland.axioms.Operators using (PlusOp)
open import net.cruhland.axioms.Peano.Base
  using () renaming (Peano to PeanoBase)
import net.cruhland.axioms.Peano.Inspect as PeanoInspect
open import net.cruhland.models.Logic using
  (_∧_; _∨_; ∨-introᴸ; ∨-introᴿ; ¬_; ¬[¬a∨¬b]→a∧b)

record Addition (PB : PeanoBase) : Set where
  open PeanoBase PB using (ℕ; ind; step; step-case; step-inj; step≄zero; zero)
  open PeanoInspect PB using (case; case-zero; case-step; decEq; pred-intro)

  field
    {{plus}} : PlusOp ℕ

  open PlusOp plus public using (_+_)

  field
    {{+-substitutiveᴸ}} : AA.Substitutiveᴸ _+_
    {{+-identityᴸ}} : AA.Identityᴸ _+_ zero
    +-stepᴸ : ∀ {n m} → step n + m ≃ step (n + m)

  instance
    +-identityᴿ : AA.Identityᴿ _+_ zero
    +-identityᴿ = record { identᴿ = +-zeroᴿ }
      where
        +-zeroᴿ : ∀ {n} → n + zero ≃ n
        +-zeroᴿ {n} = ind P Pz Ps n
          where
            P = λ x → x + zero ≃ x
            Pz = AA.identᴸ

            Ps : step-case P
            Ps {k} k+z≃k =
              begin
                step k + zero
              ≃⟨ +-stepᴸ ⟩
                step (k + zero)
              ≃⟨ AA.subst k+z≃k ⟩
                step k
              ∎

  +-stepᴿ : ∀ {n m} → n + step m ≃ step (n + m)
  +-stepᴿ {n} {m} = ind P Pz Ps n
    where
      P = λ x → x + step m ≃ step (x + m)

      Pz =
        begin
          zero + step m
        ≃⟨ AA.identᴸ ⟩
          step m
        ≃˘⟨ AA.subst AA.identᴸ ⟩
          step (zero + m)
        ∎

      Ps : step-case P
      Ps {k} k+sm≃s[k+m] =
        begin
          step k + step m
        ≃⟨ +-stepᴸ ⟩
          step (k + step m)
        ≃⟨ AA.subst k+sm≃s[k+m] ⟩
          step (step (k + m))
        ≃⟨ AA.subst (sym +-stepᴸ) ⟩
          step (step k + m)
        ∎

  +-stepᴸ⃗ᴿ : ∀ {n m} → step n + m ≃ n + step m
  +-stepᴸ⃗ᴿ = trans +-stepᴸ (sym +-stepᴿ)

  +-stepᴿ⃗ᴸ : ∀ {n m} → n + step m ≃ step n + m
  +-stepᴿ⃗ᴸ = sym +-stepᴸ⃗ᴿ

  step≃+ : ∀ {n} → step n ≃ n + step zero
  step≃+ {n} =
    begin
      step n
    ≃˘⟨ AA.subst AA.identᴿ ⟩
      step (n + zero)
    ≃˘⟨ +-stepᴿ ⟩
      n + step zero
    ∎

  instance
    +-commutative : AA.Commutative _+_
    +-commutative = record { comm = +-comm }
      where
        +-comm : ∀ {n m} → n + m ≃ m + n
        +-comm {n} {m} = ind P Pz Ps n
          where
            P = λ x → x + m ≃ m + x
            Pz =
              begin
                zero + m
              ≃⟨ AA.identᴸ ⟩
                m
              ≃˘⟨ AA.identᴿ ⟩
                m + zero
              ∎

            Ps : step-case P
            Ps {k} k+m≃m+k =
              begin
                step k + m
              ≃⟨ +-stepᴸ ⟩
                step (k + m)
              ≃⟨ AA.subst k+m≃m+k ⟩
                step (m + k)
              ≃˘⟨ +-stepᴿ ⟩
                m + step k
              ∎

    +-substitutiveᴿ : AA.Substitutiveᴿ _+_
    +-substitutiveᴿ = AA.substitutiveᴿ

    +-associative : AA.Associative _+_
    +-associative = record { assoc = +-assoc }
      where
        +-assoc : ∀ {n m p} → (n + m) + p ≃ n + (m + p)
        +-assoc {n} {m} {p} = ind P Pz Ps n
          where
            P = λ x → (x + m) + p ≃ x + (m + p)

            Pz =
              begin
                (zero + m) + p
              ≃⟨ AA.substᴸ AA.identᴸ ⟩
                m + p
              ≃˘⟨ AA.identᴸ ⟩
                zero + (m + p)
              ∎

            Ps : step-case P
            Ps {k} [k+m]+p≃k+[m+p] =
              begin
                (step k + m) + p
              ≃⟨ AA.substᴸ +-stepᴸ ⟩
                step (k + m) + p
              ≃⟨ +-stepᴸ ⟩
                step ((k + m) + p)
              ≃⟨ AA.subst [k+m]+p≃k+[m+p] ⟩
                step (k + (m + p))
              ≃⟨ sym +-stepᴸ ⟩
                step k + (m + p)
              ∎

    +-cancellativeᴸ : AA.Cancellativeᴸ _+_
    +-cancellativeᴸ = record { cancelᴸ = +-cancelᴸ }
      where
        +-cancelᴸ : ∀ {n m p} → n + m ≃ n + p → m ≃ p
        +-cancelᴸ {n} {m} {p} = ind P Pz Ps n
          where
            P = λ x → x + m ≃ x + p → m ≃ p

            Pz : P zero
            Pz z+m≃z+p =
              begin
                m
              ≃˘⟨ AA.identᴸ ⟩
                zero + m
              ≃⟨ z+m≃z+p ⟩
                zero + p
              ≃⟨ AA.identᴸ ⟩
                p
              ∎

            Ps : step-case P
            Ps {k} k+m≃k+p→m≃p sk+m≃sk+p = k+m≃k+p→m≃p (step-inj s[k+m]≃s[k+p])
              where
                s[k+m]≃s[k+p] =
                  begin
                    step (k + m)
                  ≃⟨ sym +-stepᴸ ⟩
                    step k + m
                  ≃⟨ sk+m≃sk+p ⟩
                    step k + p
                  ≃⟨ +-stepᴸ ⟩
                    step (k + p)
                  ∎

    +-cancellativeᴿ : AA.Cancellativeᴿ _+_
    +-cancellativeᴿ = AA.cancellativeᴿ

  with-+-assoc : ∀ {a b c d e} → b + c ≃ d + e → a + b + c ≃ a + d + e
  with-+-assoc {a} {b} {c} {d} {e} b+c≃d+e =
    begin
      a + b + c
    ≃⟨ AA.assoc ⟩
      a + (b + c)
    ≃⟨ AA.substᴿ b+c≃d+e ⟩
      a + (d + e)
    ≃˘⟨ AA.assoc ⟩
      a + d + e
    ∎

  n≄sn : ∀ {n} → n ≄ step n
  n≄sn {n} n≃sn = step≄zero (AA.cancelᴸ n+sz≃n+z)
    where
      n+sz≃n+z =
        begin
          n + step zero
        ≃⟨ +-stepᴿ⃗ᴸ ⟩
          step n + zero
        ≃˘⟨ AA.substᴸ n≃sn ⟩
          n + zero
        ∎

  Positive : ℕ → Set
  Positive n = n ≄ zero

  Positive-subst : ∀ {n₁ n₂} → n₁ ≃ n₂ → Positive n₁ → Positive n₂
  Positive-subst n₁≃n₂ n₁≄z n₂≃z = n₁≄z (trans n₁≃n₂ n₂≃z)

  +-positive : ∀ {a b} → Positive a → Positive (a + b)
  +-positive {a} {b} pos-a = ind P Pz Ps b
    where
      P = λ x → Positive (a + x)

      Pz : P zero
      Pz = Positive-subst (sym AA.identᴿ) pos-a

      Ps : step-case P
      Ps {k} _ = λ a+sk≃z → step≄zero (trans (sym +-stepᴿ) a+sk≃z)

  +-both-zero : ∀ {a b} → a + b ≃ zero → a ≃ zero ∧ b ≃ zero
  +-both-zero {a} {b} a+b≃z =
    ¬[¬a∨¬b]→a∧b (a ≃? zero) (b ≃? zero) neither-positive
      where
        neither-positive : ¬ (a ≄ zero ∨ b ≄ zero)
        neither-positive (∨-introᴸ a≄z) = +-positive a≄z a+b≃z
        neither-positive (∨-introᴿ b≄z) = +-positive b≄z (trans AA.comm a+b≃z)

  +-unchanged : ∀ {n m} → n + m ≃ n → m ≃ zero
  +-unchanged {n} {m} n+m≃n = AA.cancelᴸ (trans n+m≃n (sym AA.identᴿ))
