open import Function using (const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; trans; cong)
open Eq.≡-Reasoning
open import net.cruhland.axiomatic.Peano using (PeanoBundle)

module net.cruhland.axiomatic.Peano.Addition (PB : PeanoBundle) where
  open PeanoBundle PB

  _+_ : ℕ → ℕ → ℕ
  n + m = rec m succ n

  +-identityᴸ : ∀ {m} → zero + m ≡ m
  +-identityᴸ = rec-zero

  +-succᴸ : ∀ {n m} → succ n + m ≡ succ (n + m)
  +-succᴸ = rec-succ

  +-identityᴿ : ∀ {n} → n + zero ≡ n
  +-identityᴿ {n} = ind P Pz Ps n
    where
      P = λ x → x + zero ≡ x
      Pz = +-identityᴸ

      Ps : succProp P
      Ps {k} k+z≡k =
        begin
          succ k + zero
        ≡⟨ +-succᴸ ⟩
          succ (k + zero)
        ≡⟨ cong succ k+z≡k ⟩
          succ k
        ∎

  +-succᴿ : ∀ {n m} → n + succ m ≡ succ (n + m)
  +-succᴿ {n} {m} = ind P Pz Ps n
    where
      P = λ x → x + succ m ≡ succ (x + m)

      Pz =
        begin
          zero + succ m
        ≡⟨ +-identityᴸ ⟩
          succ m
        ≡⟨ cong succ (sym +-identityᴸ) ⟩
          succ (zero + m)
        ∎

      Ps : succProp P
      Ps {k} k+sm≡s[k+m] =
        begin
          succ k + succ m
        ≡⟨ +-succᴸ ⟩
          succ (k + succ m)
        ≡⟨ cong succ k+sm≡s[k+m] ⟩
          succ (succ (k + m))
        ≡⟨ cong succ (sym +-succᴸ) ⟩
          succ (succ k + m)
        ∎

  +-comm : ∀ {n m} → n + m ≡ m + n
  +-comm {n} {m} = ind P Pz Ps n
    where
      P = λ x → x + m ≡ m + x
      Pz = trans +-identityᴸ (sym +-identityᴿ)

      Ps : succProp P
      Ps {k} k+m≡m+k =
        begin
          succ k + m
        ≡⟨ +-succᴸ ⟩
          succ (k + m)
        ≡⟨ cong succ k+m≡m+k ⟩
          succ (m + k)
        ≡⟨ sym +-succᴿ ⟩
          m + succ k
        ∎

  +-assoc : ∀ {n m p} → (n + m) + p ≡ n + (m + p)
  +-assoc {n} {m} {p} = ind P Pz Ps n
    where
      P = λ x → (x + m) + p ≡ x + (m + p)

      Pz =
        begin
          (zero + m) + p
        ≡⟨ cong (_+ p) +-identityᴸ ⟩
          m + p
        ≡⟨ sym +-identityᴸ ⟩
          zero + (m + p)
        ∎

      Ps : succProp P
      Ps {k} [k+m]+p≡k+[m+p] =
        begin
          (succ k + m) + p
        ≡⟨ cong (_+ p) +-succᴸ ⟩
          succ (k + m) + p
        ≡⟨ +-succᴸ ⟩
          succ ((k + m) + p)
        ≡⟨ cong succ [k+m]+p≡k+[m+p] ⟩
          succ (k + (m + p))
        ≡⟨ sym +-succᴸ ⟩
          succ k + (m + p)
        ∎
