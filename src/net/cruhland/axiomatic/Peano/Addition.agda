open import Function using (const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong)
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
